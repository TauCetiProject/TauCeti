/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Relation
public import TauCeti.Geometry.Symplectic.Lagrangian.TwistedProd
import TauCeti.Geometry.Manifold.MFDeriv.Graph

/-!
# Composition of Lagrangian correspondences

Let `f : L₁ → M₁ × M₂` be Lagrangian for `pr₁*σ₁ - pr₂*σ₂` and `g : L₂ → M₂ × M₃` Lagrangian for
`pr₁*σ₂ - pr₂*σ₃`. Their geometric composite is the image of the fibre product
`L₁ ×_{M₂} L₂ = {(x, y) | (f x).2 = (g y).1}` under `(x, y) ↦ ((f x).1, (g y).2)` in `M₁ × M₃`.

The fibre product need not be a manifold, so the results here take a manifold `C` together
with smooth maps `a : C → L₁` and `b : C → L₂` landing in the fibre product,
`(f (a c)).2 = (g (b c)).1`, and study the composite map
`h c = ((f (a c)).1, (g (b c)).2)`. The tangent hypothesis is that `(da, db)` maps `T_c C` onto
the linear fibre product of tangent spaces: every pair `(u, w)` with `(df u).2 = (dg w).1` is
`(da ξ, db ξ)` for some `ξ`. This is the tangent property of the manifold structure on a
transverse or clean fibre product, which is not constructed here. Under it, the tangent image
of `h` at `c` is the composite of the linear canonical relations `df(T L₁)` and `dg(T L₂)`
(`Submodule.range_prod_eq_relComp_range`), which is Lagrangian by
`TauCeti.SymplecticForm.IsLagrangian.relComp`. The matching condition on tangent vectors,
`(df (da ξ)).2 = (dg (db ξ)).1`, is the derivative of the fibre-product condition
(`MDifferentiableAt.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct`). Hence
`TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp`: the composite map is
Lagrangian for `pr₁*σ₁ - pr₂*σ₃`, even when `h` has excess kernel and is not an immersion. The
embedded case, where `h` is a Lagrangian correspondence `M₁ ⇝ M₃`, is in
`TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Composition`.

The composite of the graphs of maps `φ : M₁ → M₂` and `ψ : M₂ → M₃` is the graph of `ψ ∘ φ`,
presented by `C = M₁`, `a = id` and `b = φ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianMap_graph_comp`).

## References

* A. Weinstein, *Symplectic categories*, Portugaliae Mathematica 67 (2010), 261–278.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂} {σ₃ : SmoothTwoForm I₃ M₃}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {hσ₃ : σ₃.IsNondegenerate}

/-- Linear form of the composition theorem at tangent spaces of `M₂` at two points that are equal
but not syntactically so. If `(S, T)` parametrizes the matching pairs for linear maps `A` and `B`
whose ranges are canonical relations, then `z ↦ ((A (S z)).1, (B (T z)).2)` has range a
canonical relation. -/
private theorem isLagrangian_range_prod_of_eq {x₁ : M₁} {y y' : M₂} {x₃ : M₃} (hy : y = y')
    {X Y Z : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup Z] [Module ℝ Z]
    {A : X →ₗ[ℝ] TangentSpace I₁ x₁ × TangentSpace I₂ y}
    {B : Y →ₗ[ℝ] TangentSpace I₂ y' × TangentSpace I₃ x₃} {S : Z →ₗ[ℝ] X} {T : Z →ₗ[ℝ] Y}
    (hA : ((hσ₁.symplecticFormAt x₁).twistedProd (hσ₂.symplecticFormAt y)).IsLagrangian
      (LinearMap.range A))
    (hB : ((hσ₂.symplecticFormAt y').twistedProd (hσ₃.symplecticFormAt x₃)).IsLagrangian
      (LinearMap.range B))
    (hST : ∀ z, (A (S z)).2 = (B (T z)).1)
    (hsurj : ∀ u w, (A u).2 = (B w).1 → ∃ z, S z = u ∧ T z = w) :
    ((hσ₁.symplecticFormAt x₁).twistedProd (hσ₃.symplecticFormAt x₃)).IsLagrangian
      (LinearMap.range ((LinearMap.fst ℝ _ _ ∘ₗ A ∘ₗ S).prod (LinearMap.snd ℝ _ _ ∘ₗ B ∘ₗ T))) := by
  subst hy
  rw [Submodule.range_prod_eq_relComp_range hST hsurj]
  exact hA.relComp hB

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}

/-- **Composition of Lagrangian correspondences.** Let `f : L₁ → M₁ × M₂` and
`g : L₂ → M₂ × M₃` be Lagrangian maps for the twisted products, and let `a : C → L₁`,
`b : C → L₂` land in their fibre product, `(f (a c)).2 = (g (b c)).1`. If `(da, db)` maps each
tangent space of `C` onto the pairs `(u, w)` with `(df u).2 = (dg w).1`, then the composite
`c ↦ ((f (a c)).1, (g (b c)).2)` is a Lagrangian map for `pr₁*σ₁ - pr₂*σ₃`.

The tangent hypothesis holds for transverse and for clean fibre products. No transversality or
injectivity is needed for the conclusion: the composite may have excess kernel. -/
theorem IsLagrangianMap.relComp (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w) :
    (hσ₁.twistedProd hσ₃).IsLagrangianMap KC (fun c ↦ ((f (a c)).1, (g (b c)).2)) := by
  refine (isLagrangianMap_twistedProd_iff_forall hσ₁ hσ₃).mpr fun c ↦ ?_
  let e := (Manifold.tangentSpaceProdEquiv (I := I₁) (J := I₃)
    ((f (a c)).1, (g (b c)).2)).toLinearEquiv
  let A := (Manifold.tangentSpaceProdEquiv (f (a c))).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₁ (I₁.prod I₂) f (a c)).toLinearMap
  let B := (Manifold.tangentSpaceProdEquiv (g (b c))).toLinearEquiv.toLinearMap ∘ₗ
    (mfderiv K₂ (I₂.prod I₃) g (b c)).toLinearMap
  -- `e`, `A` and `B` only change the types of tangent vectors.
  have he : ∀ v, e v = v := fun v ↦ Manifold.tangentSpaceProdEquiv_apply _ v
  have hA : ∀ u, A u = mfderiv K₁ (I₁.prod I₂) f (a c) u :=
    fun u ↦ Manifold.tangentSpaceProdEquiv_apply _ _
  have hB : ∀ w, B w = mfderiv K₂ (I₂.prod I₃) g (b c) w :=
    fun w ↦ Manifold.tangentSpaceProdEquiv_apply _ _
  have hfa : MDifferentiableAt KC (I₁.prod I₂) (f ∘ a) c := (hf (a c)).comp c (ha c)
  have hgb : MDifferentiableAt KC (I₂.prod I₃) (g ∘ b) c := (hg (b c)).comp c (hb c)
  have hh : MDifferentiableAt KC (I₁.prod I₃) (fun c ↦ ((f (a c)).1, (g (b c)).2)) c :=
    hfa.fst.prodMk hgb.snd
  -- The tangent map of the composite reads off the outer coordinates of `df (da ξ)` and
  -- `dg (db ξ)`.
  have hd : e.toLinearMap ∘ₗ
      (mfderiv KC (I₁.prod I₃) (fun c ↦ ((f (a c)).1, (g (b c)).2)) c).toLinearMap =
      (LinearMap.fst ℝ _ _ ∘ₗ A ∘ₗ (mfderiv KC K₁ a c).toLinearMap).prod
        (LinearMap.snd ℝ _ _ ∘ₗ B ∘ₗ (mfderiv KC K₂ b c).toLinearMap) := by
    ext ξ
    · simp only [LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, he, hA]
      rw [← hh.mfderiv_fst_apply, ← mfderiv_comp_apply c (hf (a c)) (ha c)]
      -- `LinearMap.fst` is the projection by definition, but `LinearMap.fst_apply` does not
      -- rewrite here: it acts on the product of the coordinate tangent spaces, which is the
      -- tangent space of the product only by definition.
      exact hfa.mfderiv_fst_apply ξ
    · simp only [LinearMap.comp_apply, LinearMap.prod_apply, Function.prod_apply,
        ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe, he, hB]
      rw [← hh.mfderiv_snd_apply, ← mfderiv_comp_apply c (hg (b c)) (hb c)]
      -- `LinearMap.snd` is the projection by definition, but `LinearMap.snd_apply` does not
      -- rewrite here: it acts on the product of the coordinate tangent spaces, which is the
      -- tangent space of the product only by definition.
      exact hgb.mfderiv_snd_apply ξ
  rw [hd]
  -- The tangent image is the composite of the tangent relations of `f` and `g`.
  refine isLagrangian_range_prod_of_eq (hσ₂ := hσ₂) (hab c)
    ((isLagrangianMap_twistedProd_iff_forall hσ₁ hσ₂).mp hfL (a c))
    ((isLagrangianMap_twistedProd_iff_forall hσ₂ hσ₃).mp hgL (b c)) (fun ξ ↦ ?_)
    (fun u w h ↦ hfib c u w ?_)
  · rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe, hA, hB,
      ← mfderiv_comp_apply c (hf (a c)) (ha c), ← mfderiv_comp_apply c (hg (b c)) (hb c)]
    exact hfa.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct hgb hab ξ
  · rwa [hA, hB] at h

/-- **Composition of graphs.** If the graphs of smooth maps `φ : M₁ → M₂` and `ψ : M₂ → M₃` are
Lagrangian for the twisted products, so is the graph of `ψ ∘ φ`. This is the composite of the two
graph correspondences, presented over `C = M₁` by `a = id` and `b = φ`. -/
theorem isLagrangianMap_graph_comp {φ : M₁ → M₂} {ψ : M₂ → M₃} (hφ : MDifferentiable I₁ I₂ φ)
    (hψ : MDifferentiable I₂ I₃ ψ)
    (h₁ : (hσ₁.twistedProd hσ₂).IsLagrangianMap I₁ (fun x ↦ (x, φ x)))
    (h₂ : (hσ₂.twistedProd hσ₃).IsLagrangianMap I₂ (fun y ↦ (y, ψ y))) :
    (hσ₁.twistedProd hσ₃).IsLagrangianMap I₁ (fun x ↦ (x, ψ (φ x))) :=
  h₁.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) (a := id) (b := φ) h₂
    (mdifferentiable_id.prodMk hφ) (mdifferentiable_id.prodMk hψ)
    mdifferentiable_id hφ (fun _ ↦ rfl) fun x u w h ↦ ⟨u, by simp, by
      rw [Manifold.mfderiv_graph_snd_apply (hφ _), Manifold.mfderiv_graph_fst_apply (hψ _)] at h
      exact h⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
