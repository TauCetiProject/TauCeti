/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.DiracType
import Mathlib.Topology.VectorBundle.FiniteDimensional
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Dual

/-!
# Elliptic differential operators between vector bundles

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff manifold `M`,
with `V` of finite rank, and let `P : Γ(V) → Γ(W)` be a differential operator of order at most `m`
in Grothendieck's sense (`TauCeti.differentialOperators`). The operator is *elliptic* at a point
`x` (`TauCeti.IsSectionEllipticAt`) if its principal symbol `σ(P)(ξ) : V_x → W_x`
(`TauCeti.sectionPrincipalSymbol`) is bijective at every nonzero covector `ξ ∈ T_x*M`, and
*elliptic* (`TauCeti.IsSectionElliptic`) if it is elliptic at every point. The principal symbol is
taken in the geometric convention; the Fourier principal symbol `σ_F(P) = i ^ m σ_geom(P)` of the
complexified operator is bijective at the same covectors, so the notion does not depend on the
convention. Ellipticity is the hypothesis of the elliptic regularity and Fredholm theory of `P`.

Ellipticity is a condition at the top order only: it is unchanged by adding an operator of lower
order and by multiplying by a nonzero constant, and it is preserved by composition, since principal
symbols multiply (`TauCeti.sectionPrincipalSymbol_comp`). For fibre metrics and a measure positive
on open sets, a formal adjoint of `P` is elliptic exactly when `P` is, since its principal symbol is
`(-1) ^ m` times the fibrewise adjoint of that of `P`
(`LinearMap.IsFormalAdjoint.inner_sectionPrincipalSymbol_apply`).

Over a manifold of positive dimension the cotangent spaces contain nonzero covectors, so an
elliptic operator identifies the fibres `V_x ≅ W_x` through its symbol, and the two bundles have
the same rank. In dimension zero every covector vanishes and every operator is elliptic, whatever
the ranks. Likewise, in positive dimension and over a nonzero fibre, an elliptic operator of order
at most `m + 1` does not have order at most `m`; in particular the zero operator is not elliptic.

Operators of Laplace type (`TauCeti.IsSectionLaplaceType`), such as the rough Laplacian `∇*∇`
(`CovariantDerivative.isSectionLaplaceType_smoothRoughLaplacian`), are elliptic. An operator of
Dirac type (`TauCeti.IsDiracType`) has injective principal symbol at nonzero covectors, so it is
elliptic when its two bundles have the same rank; over a manifold of positive dimension it is
elliptic at an interior point exactly when they do.

## Main definitions

* `TauCeti.IsSectionEllipticAt P x`: the principal symbol of `P` is bijective at every nonzero
  covector at `x`.
* `TauCeti.IsSectionElliptic P`: `P` is elliptic at every point.

## Main results

* `TauCeti.IsSectionEllipticAt.finrank_eq`: in positive dimension, an operator elliptic at an
  interior point is a map between bundles of equal rank.
* `TauCeti.isSectionEllipticAt_of_subsingleton`: in dimension zero every operator is elliptic.
* `TauCeti.IsSectionEllipticAt.notMem_differentialOperators`: in positive dimension, over a nonzero
  fibre, an elliptic operator of order at most `m + 1` does not have order at most `m`.
* `TauCeti.isSectionEllipticAt_add_iff`: ellipticity is unchanged by perturbations of lower order.
* `TauCeti.IsSectionEllipticAt.comp`: the composition of elliptic operators is elliptic.
* `LinearMap.IsFormalAdjoint.isSectionEllipticAt_iff`: a formal adjoint of `P` is elliptic exactly
  when `P` is.
* `TauCeti.IsSectionLaplaceType.isSectionElliptic`: operators of Laplace type are elliptic.
* `TauCeti.IsDiracType.isSectionEllipticAt_iff`: in positive dimension, an operator of Dirac type
  is elliptic exactly when its two bundles have the same rank.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators I*, Ann. of Math. 87 (1968),
  §5 (elliptic symbols and operators).
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (elliptic differential operators and their symbols).
* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter III,
  §1 (the ellipticity of Dirac operators).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {m : ℕ} {x : M}

/-- A differential operator `P : Γ(V) → Γ(W)` of order at most `m` between the smooth sections of
two vector bundles is **elliptic at** `x` if, provided `x` is an interior point, its principal
symbol `σ(P)(ξ) : V_x → W_x` (`TauCeti.sectionPrincipalSymbol`) is bijective at every nonzero
covector `ξ ∈ T_x*M`. At a boundary point the condition is empty. -/
def IsSectionEllipticAt
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) (x : M) : Prop :=
  ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
    Function.Bijective (sectionPrincipalSymbol I hx P ξ)

/-- A differential operator `P : Γ(V) → Γ(W)` of order at most `m` is **elliptic** if it is
elliptic at every point (`TauCeti.IsSectionEllipticAt`): its principal symbol is bijective at every
nonzero covector at every interior point. -/
def IsSectionElliptic
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) : Prop :=
  ∀ x, IsSectionEllipticAt P x

variable {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}

theorem isSectionEllipticAt_iff : IsSectionEllipticAt P x ↔
    ∀ (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ), ξ ≠ 0 →
      Function.Bijective (sectionPrincipalSymbol I hx P ξ) :=
  Iff.rfl

theorem isSectionElliptic_iff : IsSectionElliptic P ↔ ∀ x, IsSectionEllipticAt P x :=
  Iff.rfl

/-- The principal symbol of an operator elliptic at `x` is bijective at every nonzero covector. -/
theorem IsSectionEllipticAt.sectionPrincipalSymbol_bijective (hP : IsSectionEllipticAt P x)
    (hx : I.IsInteriorPoint x) {ξ : TangentSpace I x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    Function.Bijective (sectionPrincipalSymbol I hx P ξ) :=
  hP hx ξ hξ

/-- Between bundles of the same rank, an injective principal symbol is bijective. -/
theorem sectionPrincipalSymbol_bijective_of_injective [FiniteDimensional ℝ F']
    (hF : Module.finrank ℝ F = Module.finrank ℝ F') (hx : I.IsInteriorPoint x)
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : Function.Injective (sectionPrincipalSymbol I hx P ξ)) :
    Function.Bijective (sectionPrincipalSymbol I hx P ξ) := by
  have := VectorBundle.finiteDimensional ℝ F V x
  have := VectorBundle.finiteDimensional ℝ F' W x
  refine ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 h⟩
  rw [VectorBundle.finrank_eq ℝ F V x, VectorBundle.finrank_eq ℝ F' W x, hF]

/-- **Dimension zero.** Over a manifold modelled on the zero space, every cotangent vector vanishes,
so every operator is elliptic, whatever the ranks of the two bundles. -/
theorem isSectionEllipticAt_of_subsingleton [Subsingleton E] : IsSectionEllipticAt P x :=
  fun _ ξ hξ ↦ absurd (Subsingleton.elim ξ 0) hξ

/-- **Ellipticity forces equal ranks.** Over a manifold of positive dimension, if `P` is elliptic
at an interior point, then `V` and `W` have the same rank: the principal symbol at a nonzero
covector is a linear isomorphism `V_x ≃ W_x`. -/
theorem IsSectionEllipticAt.finrank_eq [Nontrivial E] (hP : IsSectionEllipticAt P x)
    (hx : I.IsInteriorPoint x) : Module.finrank ℝ F = Module.finrank ℝ F' := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  rw [← VectorBundle.finrank_eq ℝ F V x, ← VectorBundle.finrank_eq ℝ F' W x]
  exact (LinearEquiv.ofBijective _ (hP.sectionPrincipalSymbol_bijective hx hξ)).finrank_eq

/-- **Ellipticity forces equal ranks.** Over a nonempty boundaryless manifold of positive
dimension, the two bundles of an elliptic operator have the same rank. -/
theorem IsSectionElliptic.finrank_eq [Nontrivial E] [BoundarylessManifold I M] [Nonempty M]
    (hP : IsSectionElliptic P) : Module.finrank ℝ F = Module.finrank ℝ F' :=
  (hP (Classical.arbitrary M)).finrank_eq BoundarylessManifold.isInteriorPoint

/-- Over a nonzero fibre, the principal symbol of an operator elliptic at `x` does not vanish at
any nonzero covector. -/
theorem IsSectionEllipticAt.sectionPrincipalSymbol_ne_zero [Nontrivial F]
    (hP : IsSectionEllipticAt P x) (hx : I.IsInteriorPoint x) {ξ : TangentSpace I x →L[ℝ] ℝ}
    (hξ : ξ ≠ 0) : sectionPrincipalSymbol I hx P ξ ≠ 0 := by
  have : Nontrivial (V x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F V x).symm.injective.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V x)
  intro h
  refine hv ((hP.sectionPrincipalSymbol_bijective hx hξ).injective ?_)
  rw [h, LinearMap.zero_apply, map_zero]

/-- **Elliptic operators have exact order.** Over a manifold of positive dimension and a nonzero
fibre, an operator of order at most `m + 1` which is elliptic at an interior point does not have
order at most `m`: its principal symbol would vanish. -/
theorem IsSectionEllipticAt.notMem_differentialOperators [Nontrivial E] [Nontrivial F]
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)}
    (hP : IsSectionEllipticAt P x) (hx : I.IsInteriorPoint x) :
    (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∉
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m := fun hm ↦ by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  exact hP.sectionPrincipalSymbol_ne_zero hx hξ
    (sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators hx P hm ξ)

/-- Over a manifold of positive dimension and a nonzero fibre, the zero operator is not elliptic
at any interior point. -/
theorem not_isSectionEllipticAt_zero [Nontrivial E] [Nontrivial F] (hx : I.IsInteriorPoint x) :
    ¬IsSectionEllipticAt (0 : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
      x := fun h ↦ by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : TangentSpace I x →L[ℝ] ℝ)
  exact h.sectionPrincipalSymbol_ne_zero hx hξ (sectionPrincipalSymbol_zero hx ξ)

/-! ### Operations preserving ellipticity -/

/-- Multiplying an operator by a nonzero constant does not change its ellipticity. -/
theorem isSectionEllipticAt_smul_iff {c : ℝ} (hc : c ≠ 0) :
    IsSectionEllipticAt (c • P) x ↔ IsSectionEllipticAt P x := by
  have hb (hx : I.IsInteriorPoint x) (ξ : TangentSpace I x →L[ℝ] ℝ) :
      Function.Bijective (sectionPrincipalSymbol I hx (c • P) ξ) ↔
        Function.Bijective (sectionPrincipalSymbol I hx P ξ) := by
    have h : ⇑(sectionPrincipalSymbol I hx (c • P) ξ) =
        LinearEquiv.smulOfNeZero ℝ (W x) c hc ∘ sectionPrincipalSymbol I hx P ξ := by
      ext v
      simp
    rw [h, EquivLike.comp_bijective]
  simp only [isSectionEllipticAt_iff, hb]

theorem IsSectionEllipticAt.smul (hP : IsSectionEllipticAt P x) {c : ℝ} (hc : c ≠ 0) :
    IsSectionEllipticAt (c • P) x :=
  (isSectionEllipticAt_smul_iff hc).2 hP

/-- Multiplying an operator by a nonzero constant does not change its ellipticity. -/
theorem isSectionElliptic_smul_iff {c : ℝ} (hc : c ≠ 0) :
    IsSectionElliptic (c • P) ↔ IsSectionElliptic P :=
  forall_congr' fun _ ↦ isSectionEllipticAt_smul_iff hc

theorem IsSectionElliptic.smul (hP : IsSectionElliptic P) {c : ℝ} (hc : c ≠ 0) :
    IsSectionElliptic (c • P) :=
  (isSectionElliptic_smul_iff hc).2 hP

@[simp]
theorem isSectionEllipticAt_neg : IsSectionEllipticAt (-P) x ↔ IsSectionEllipticAt P x := by
  rw [← neg_one_smul ℝ P, isSectionEllipticAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

@[simp]
theorem isSectionElliptic_neg : IsSectionElliptic (-P) ↔ IsSectionElliptic P := by
  simp [isSectionElliptic_iff]

/-- **Perturbations of lower order.** Adding an operator of order at most `m` to an operator of
order at most `m + 1` does not change its ellipticity, since it does not change its principal
symbol. -/
theorem isSectionEllipticAt_add_iff
    {P Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)}
    (hQ : (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    IsSectionEllipticAt (P + Q) x ↔ IsSectionEllipticAt P x := by
  simp only [isSectionEllipticAt_iff, sectionPrincipalSymbol_add,
    sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators _ Q hQ, add_zero]

/-- **Perturbations of lower order.** Adding an operator of order at most `m` to an operator of
order at most `m + 1` elliptic at `x` gives an operator elliptic at `x`. -/
theorem IsSectionEllipticAt.add
    {P Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)}
    (hP : IsSectionEllipticAt P x)
    (hQ : (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    IsSectionEllipticAt (P + Q) x :=
  (isSectionEllipticAt_add_iff hQ).2 hP

/-- **Perturbations of lower order.** Adding an operator of order at most `m` to an operator of
order at most `m + 1` does not change its ellipticity. -/
theorem isSectionElliptic_add_iff
    {P Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)}
    (hQ : (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    IsSectionElliptic (P + Q) ↔ IsSectionElliptic P :=
  forall_congr' fun _ ↦ isSectionEllipticAt_add_iff hQ

/-- **Perturbations of lower order.** Adding an operator of order at most `m` to an elliptic
operator of order at most `m + 1` gives an elliptic operator. -/
theorem IsSectionElliptic.add
    {P Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)}
    (hP : IsSectionElliptic P)
    (hQ : (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    IsSectionElliptic (P + Q) :=
  (isSectionElliptic_add_iff hQ).2 hP

section Comp

variable [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  {U : M → Type*} [TopologicalSpace (TotalSpace F'' U)]
  [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)] [∀ x, TopologicalSpace (U x)]
  [FiberBundle F'' U] [VectorBundle ℝ F'' U] {k : ℕ}

/-- **Composition.** If `P : Γ(W) → Γ(U)` and `Q : Γ(V) → Γ(W)` are elliptic at `x`, then so is
`P ∘ Q`, as an operator of order at most `m + k`: its principal symbol is the composition of
theirs. -/
theorem IsSectionEllipticAt.comp
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F'', U⟯ m}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ k}
    (hP : IsSectionEllipticAt P x) (hQ : IsSectionEllipticAt Q x) :
    IsSectionEllipticAt
      ⟨(P : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) ∘ₗ (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
        comp_mem_differentialOperators P.property Q.property⟩ x := by
  intro hx ξ hξ
  rw [sectionPrincipalSymbol_comp, LinearMap.coe_comp]
  exact (hP.sectionPrincipalSymbol_bijective hx hξ).comp (hQ.sectionPrincipalSymbol_bijective hx hξ)

/-- **Composition.** The composition of elliptic operators is elliptic. -/
theorem IsSectionElliptic.comp
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F'', U⟯ m}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ k}
    (hP : IsSectionElliptic P) (hQ : IsSectionElliptic Q) :
    IsSectionElliptic
      ⟨(P : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) ∘ₗ (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
        comp_mem_differentialOperators P.property Q.property⟩ :=
  fun x ↦ (hP x).comp (hQ x)

end Comp

/-! ### Operators of Laplace type -/

/-- **Operators of Laplace type are elliptic**: their principal symbol `-(c ‖ξ‖²) Id` is
invertible at every nonzero covector. -/
theorem IsSectionLaplaceType.isSectionElliptic [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2} {c : ℝ}
    (hP : IsSectionLaplaceType P c) : IsSectionElliptic P :=
  fun _ hx _ hξ ↦ hP.sectionPrincipalSymbol_bijective hx hξ

end TauCeti

/-! ### Formal adjoints and operators of Dirac type -/

section Metric

open MeasureTheory TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {m : ℕ} {x : M}

namespace LinearMap

variable [ContMDiffVectorBundle ∞ F' W I] [SigmaCompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsContinuousRiemannianBundle F V] [IsContinuousRiemannianBundle F' W]
  {μ : Measure M} [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
  {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
  {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ m}

/-- A formal adjoint of an operator elliptic at `x` is elliptic at `x`: at a nonzero covector its
principal symbol is `(-1) ^ m` times the fibrewise adjoint of the bijective symbol of `P`. -/
theorem IsFormalAdjoint.isSectionEllipticAt
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ)
    (hP : IsSectionEllipticAt P x) : IsSectionEllipticAt Q x := by
  intro hx ξ hξ
  have hA := hP.sectionPrincipalSymbol_bijective hx hξ
  -- The symbol of `Q` is injective: if it kills `w`, then `w` is orthogonal to the range of the
  -- symbol of `P`, which is everything.
  have hinj : Function.Injective (sectionPrincipalSymbol I hx Q ξ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨v, rfl⟩ := hA.surjective w
    have hi := h.inner_sectionPrincipalSymbol_apply hx ξ v (sectionPrincipalSymbol I hx P ξ v)
    rw [hw, inner_zero_right, mul_zero] at hi
    exact inner_self_eq_zero.1 hi
  -- It is then bijective, the bundles having the same rank: the dimension is positive, since
  -- there is a nonzero covector.
  have : Nontrivial E := not_subsingleton_iff_nontrivial.1 fun _ ↦ hξ (Subsingleton.elim ξ 0)
  exact sectionPrincipalSymbol_bijective_of_injective (hP.finrank_eq hx).symm hx hinj

/-- **Formal adjoints of elliptic operators.** If `Q` is a formal adjoint of `P`, then `Q` is
elliptic at `x` exactly when `P` is. -/
theorem IsFormalAdjoint.isSectionEllipticAt_iff
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ) :
    IsSectionEllipticAt Q x ↔ IsSectionEllipticAt P x :=
  ⟨h.symm.isSectionEllipticAt, h.isSectionEllipticAt⟩

/-- **Formal adjoints of elliptic operators.** If `Q` is a formal adjoint of `P`, then `Q` is
elliptic exactly when `P` is. -/
theorem IsFormalAdjoint.isSectionElliptic_iff
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint
      (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) μ) :
    IsSectionElliptic Q ↔ IsSectionElliptic P :=
  forall_congr' fun _ ↦ h.isSectionEllipticAt_iff

end LinearMap

namespace TauCeti

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1}

/-- An operator of Dirac type between bundles of the same rank is elliptic: its principal symbol
at a nonzero covector is injective, hence bijective. -/
theorem IsDiracType.isSectionElliptic (hD : IsDiracType D)
    (hF : Module.finrank ℝ F = Module.finrank ℝ F') : IsSectionElliptic D :=
  fun _ hx _ hξ ↦
    sectionPrincipalSymbol_bijective_of_injective hF hx (hD.sectionPrincipalSymbol_injective hx hξ)

/-- **Ellipticity of operators of Dirac type.** Over a manifold of positive dimension, an operator
of Dirac type is elliptic at an interior point exactly when its two bundles have the same rank. -/
theorem IsDiracType.isSectionEllipticAt_iff [Nontrivial E] (hD : IsDiracType D)
    (hx : I.IsInteriorPoint x) :
    IsSectionEllipticAt D x ↔ Module.finrank ℝ F = Module.finrank ℝ F' :=
  ⟨fun h ↦ h.finrank_eq hx, fun hF ↦ hD.isSectionElliptic hF x⟩

end TauCeti

end Metric
