/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Relation
public import TauCeti.Geometry.Symplectic.Manifold.TwistedProd

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
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_snd_eq_mfderiv_fst_of_fiberProduct`). Hence:

* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianMap.relComp`: the composite map is
  Lagrangian for `pr₁*σ₁ - pr₂*σ₃`, even when `h` has excess kernel and is not an immersion;
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianEmbedding.relComp`: when moreover `h` is a
  smooth embedding, the composite is a Lagrangian correspondence `M₁ ⇝ M₃`.

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

/-- A Lagrangian map into a twisted product has tangent images that are linear canonical
relations, after the canonical identification `T(M × N) = TM × TN`. -/
private theorem isLagrangian_range_prod {E H M F G N EL HL L : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
    [NormedAddCommGroup EL] [NormedSpace ℝ EL] [TopologicalSpace HL]
    {K : ModelWithCorners ℝ EL HL} [TopologicalSpace L] [ChartedSpace HL L]
    {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} {hσ : σ.IsNondegenerate}
    {hτ : τ.IsNondegenerate} {f : L → M × N} (hf : (hσ.twistedProd hτ).IsLagrangianMap K f)
    (x : L) :
    ((hσ.symplecticFormAt (f x).1).twistedProd (hτ.symplecticFormAt (f x).2)).IsLagrangian
      (LinearMap.range ((Manifold.tangentSpaceProdEquiv (f x)).toLinearEquiv.toLinearMap ∘ₗ
        (mfderiv K (I.prod J) f x).toLinearMap)) := by
  rw [LinearMap.range_comp, ← symplecticFormAt_twistedProd hσ hτ,
    SymplecticForm.isLagrangian_map_transport_iff]
  exact isLagrangianMap_iff_forall.mp hf x

variable {EL₁ HL₁ L₁ EL₂ HL₂ L₂ EC HC C : Type*}
  [NormedAddCommGroup EL₁] [NormedSpace ℝ EL₁] [TopologicalSpace HL₁]
  {K₁ : ModelWithCorners ℝ EL₁ HL₁} [TopologicalSpace L₁] [ChartedSpace HL₁ L₁]
  [NormedAddCommGroup EL₂] [NormedSpace ℝ EL₂] [TopologicalSpace HL₂]
  {K₂ : ModelWithCorners ℝ EL₂ HL₂} [TopologicalSpace L₂] [ChartedSpace HL₂ L₂]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC] [TopologicalSpace HC]
  {KC : ModelWithCorners ℝ EC HC} [TopologicalSpace C] [ChartedSpace HC C]
  {f : L₁ → M₁ × M₂} {g : L₂ → M₂ × M₃} {a : C → L₁} {b : C → L₂}

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [IsManifold I₂ ∞ M₂] in
/-- The differential of `c ↦ (f (a c)).1` is the first coordinate of `df (da ξ)`. -/
private theorem mfderiv_fst_comp_apply (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (ha : MDifferentiable KC K₁ a) (c : C) (ξ : TangentSpace KC c) :
    mfderiv KC I₁ (fun c ↦ (f (a c)).1) c ξ =
      (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1 := by
  rw [show (fun c ↦ (f (a c)).1) = Prod.fst ∘ f ∘ a from rfl,
    mfderiv_comp_apply c mdifferentiableAt_fst ((hf (a c)).comp c (ha c)), mfderiv_fst,
    mfderiv_comp_apply c (hf (a c)) (ha c)]
  rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [IsManifold I₂ ∞ M₂] in
/-- The differential of `c ↦ (f (a c)).2` is the second coordinate of `df (da ξ)`. -/
private theorem mfderiv_snd_comp_apply (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (ha : MDifferentiable KC K₁ a) (c : C) (ξ : TangentSpace KC c) :
    mfderiv KC I₂ (fun c ↦ (f (a c)).2) c ξ =
      (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).2 := by
  rw [show (fun c ↦ (f (a c)).2) = Prod.snd ∘ f ∘ a from rfl,
    mfderiv_comp_apply c mdifferentiableAt_snd ((hf (a c)).comp c (ha c)), mfderiv_snd,
    mfderiv_comp_apply c (hf (a c)) (ha c)]
  rfl

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ E₃]
  [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃] in
/-- The differential of the outer composite `c ↦ ((f (a c)).1, (g (b c)).2)` reads off the outer
coordinates of `df (da ξ)` and `dg (db ξ)`. -/
private theorem mfderiv_relComp_apply (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (c : C) (ξ : TangentSpace KC c) :
    mfderiv KC (I₁.prod I₃) (fun c ↦ ((f (a c)).1, (g (b c)).2)) c ξ =
      ((mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).1,
        (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).2) := by
  have h₁ : MDifferentiableAt KC I₁ (fun c ↦ (f (a c)).1) c :=
    mdifferentiableAt_fst.comp c ((hf (a c)).comp c (ha c))
  have h₃ : MDifferentiableAt KC I₃ (fun c ↦ (g (b c)).2) c :=
    mdifferentiableAt_snd.comp c ((hg (b c)).comp c (hb c))
  rw [mfderiv_prodMk h₁ h₃]
  exact Prod.ext (mfderiv_fst_comp_apply hf ha c ξ) (mfderiv_snd_comp_apply hg hb c ξ)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ E₃]
  [IsManifold I₁ ∞ M₁] [IsManifold I₂ ∞ M₂] [IsManifold I₃ ∞ M₃] in
/-- Differentiating the fibre-product condition `(f (a c)).2 = (g (b c)).1`: the middle
coordinates of `df (da ξ)` and `dg (db ξ)` agree. -/
theorem mfderiv_snd_eq_mfderiv_fst_of_fiberProduct (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (hab : ∀ c, (f (a c)).2 = (g (b c)).1) (c : C)
    (ξ : TangentSpace KC c) :
    (mfderiv K₁ (I₁.prod I₂) f (a c) (mfderiv KC K₁ a c ξ)).2 =
      (mfderiv K₂ (I₂.prod I₃) g (b c) (mfderiv KC K₂ b c ξ)).1 := by
  rw [← mfderiv_snd_comp_apply hf ha c ξ, ← mfderiv_fst_comp_apply hg hb c ξ]
  exact congrArg (fun φ : C → M₂ ↦ (mfderiv KC I₂ φ c ξ : E₂)) (funext hab)

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
  rw [isLagrangianMap_iff_forall]
  intro c
  let e := (Manifold.tangentSpaceProdEquiv (I := I₁) (J := I₃)
    ((f (a c)).1, (g (b c)).2)).toLinearEquiv
  rw [← SymplecticForm.isLagrangian_map_transport_iff (e := e),
    symplecticFormAt_twistedProd hσ₁ hσ₃, ← LinearMap.range_comp]
  -- The tangent image is the composite of the tangent relations of `f` and `g`.
  convert isLagrangian_range_prod_of_eq (hσ₂ := hσ₂) (hab c) (isLagrangian_range_prod hfL (a c))
    (isLagrangian_range_prod hgL (b c)) (S := (mfderiv KC K₁ a c).toLinearMap)
    (T := (mfderiv KC K₂ b c).toLinearMap)
    (fun ξ ↦ by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, Manifold.tangentSpaceProdEquiv_apply]
      exact mfderiv_snd_eq_mfderiv_fst_of_fiberProduct hf hg ha hb hab c ξ)
    (fun u w h ↦ hfib c u w (by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
        ContinuousLinearEquiv.coe_toLinearEquiv, Manifold.tangentSpaceProdEquiv_apply] at h
      exact h)) using 2
  ext ξ <;>
  · simp only [e, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv, Manifold.tangentSpaceProdEquiv_apply]
    simp [mfderiv_relComp_apply hf hg ha hb c ξ]
    -- The two sides differ only in the elaborated types of the middle tangent spaces.
    rfl

/-- **Composition of Lagrangian correspondences, embedded case.** Under the hypotheses of
`IsLagrangianMap.relComp`, if the composite `c ↦ ((f (a c)).1, (g (b c)).2)` is moreover a smooth
embedding, it is a Lagrangian correspondence `M₁ ⇝ M₃`. -/
theorem IsLagrangianEmbedding.relComp (hfL : (hσ₁.twistedProd hσ₂).IsLagrangianMap K₁ f)
    (hgL : (hσ₂.twistedProd hσ₃).IsLagrangianMap K₂ g) (hf : MDifferentiable K₁ (I₁.prod I₂) f)
    (hg : MDifferentiable K₂ (I₂.prod I₃) g) (ha : MDifferentiable KC K₁ a)
    (hb : MDifferentiable KC K₂ b) (hab : ∀ c, (f (a c)).2 = (g (b c)).1)
    (hfib : ∀ c u w, (mfderiv K₁ (I₁.prod I₂) f (a c) u).2 =
        (mfderiv K₂ (I₂.prod I₃) g (b c) w).1 →
      ∃ ξ, mfderiv KC K₁ a c ξ = u ∧ mfderiv KC K₂ b c ξ = w)
    (hemb : Manifold.IsSmoothEmbedding KC (I₁.prod I₃) ∞
      (fun c ↦ ((f (a c)).1, (g (b c)).2))) :
    (hσ₁.twistedProd hσ₃).IsLagrangianEmbedding KC (fun c ↦ ((f (a c)).1, (g (b c)).2)) :=
  (isLagrangianEmbedding_iff_of_isSmoothEmbedding hemb).mpr
    (hfL.relComp (hσ₁ := hσ₁) (hσ₂ := hσ₂) (hσ₃ := hσ₃) hgL hf hg ha hb hab hfib)

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [IsManifold I₂ ∞ M₂] in
/-- The differential of the graph `x ↦ (x, φ x)` has first coordinate `u`. -/
private theorem mfderiv_graph_fst_apply {φ : M₁ → M₂} (hφ : MDifferentiable I₁ I₂ φ) (x : M₁)
    (u : TangentSpace I₁ x) : (mfderiv I₁ (I₁.prod I₂) (fun x ↦ (x, φ x)) x u).1 = u := by
  rw [mfderiv_prodMk (f := fun x : M₁ ↦ x) mdifferentiableAt_id (hφ x)]
  exact DFunLike.congr_fun (mfderiv_id (I := I₁) (x := x)) u

omit [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [IsManifold I₁ ∞ M₁]
  [IsManifold I₂ ∞ M₂] in
/-- The differential of the graph `x ↦ (x, φ x)` has second coordinate `dφ u`. -/
private theorem mfderiv_graph_snd_apply {φ : M₁ → M₂} (hφ : MDifferentiable I₁ I₂ φ) (x : M₁)
    (u : TangentSpace I₁ x) :
    (mfderiv I₁ (I₁.prod I₂) (fun x ↦ (x, φ x)) x u).2 = mfderiv I₁ I₂ φ x u := by
  rw [mfderiv_prodMk (f := fun x : M₁ ↦ x) mdifferentiableAt_id (hφ x)]
  rfl

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
      rw [mfderiv_graph_snd_apply hφ, mfderiv_graph_fst_apply hψ] at h
      exact h⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
