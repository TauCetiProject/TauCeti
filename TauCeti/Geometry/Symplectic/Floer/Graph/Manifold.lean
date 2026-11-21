/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Symplectic.Floer.Graph.Basic
public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# Gromov's graph construction for the Floer equation in a manifold

Let `ω` be a two-form on a manifold `M`, `J(z, x)` almost complex structures on the tangent
spaces `T_x M` depending on a domain point `z = (s, t)`, and `K = K_s ds + K_t dt` a Hamiltonian
perturbation with Hamiltonian one-form `X_K(z, x) = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}`
(`TauCeti.SmoothTwoForm.hamiltonianOneForm`). This file is the manifold-target counterpart of
`TauCeti.Geometry.Symplectic.Floer.Graph.Basic`. On the product manifold `(ℝ × ℝ) × M`, whose
tangent space at `p = (z, x)` is `(ℝ × ℝ) × T_x M`, put Gromov's structure

`J_K(z, x)(ξ, v) = (j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`,

the skew product of the standard structure `j` of `ℝ × ℝ` and `J(z, x)` along `X_K(z, x)`
(`TauCeti.SmoothTwoForm.floerGraphAlmostComplex`). Then, pointwise:

* a map `u : ℝ × ℝ → M` solves the Floer equation `(du - X_K)^{0,1} = 0` at `z` exactly when its
  graph `w ↦ (w, u w)` has a manifold derivative at `z` which is complex linear from `j` to `J_K`
  (`TauCeti.SmoothTwoForm.exists_hasMFDerivAt_graph_isComplexLinearMap_iff`);
* the projection to `ℝ × ℝ` of a map whose derivative is complex linear into `J_K` has derivative
  complex linear into `j` (`TauCeti.SmoothTwoForm.exists_hasMFDerivAt_fst_isComplexLinearMap`);
* a map `y ↦ (z, g y)` into the fibre `{z} × M` over a fixed domain point has a derivative complex
  linear into `J_K` exactly when `g` has one complex linear into the structure `J(z, ·)` frozen
  at `z` (`TauCeti.SmoothTwoForm.exists_hasMFDerivAt_prodMk_isComplexLinearMap_iff`). So the
  vertical components of a `J_K`-holomorphic curve, such as the spheres bubbling off a sequence of
  Floer solutions at a domain point `z`, are holomorphic for `J` frozen at `z`, not for an
  unrelated global structure.

For a constant `c` consider the two-form `Ω_c = pr₂^* ω + dK + c ds ∧ dt` on `(ℝ × ℝ) × M`, where
`dK` is the exterior derivative of the one-form `K_s ds + K_t dt`; its value on tangent vectors
`ζ`, `ζ'` is computed from the derivatives of `K_s` and `K_t` on the product
(`TauCeti.SmoothTwoForm.floerGraphForm`). For a fibrewise nondegenerate `ω` the curvature
`R_K = ∂_s K_t - ∂_t K_s - {K_s, K_t}` measures how far it is from a split form:

`Ω_c((ξ, v), (ξ', v')) = ω(v - X_K ξ, v' - X_K ξ') + (c + R_K) (ds ∧ dt)(ξ, ξ')`

(`TauCeti.SmoothTwoForm.IsNondegenerate.floerGraphForm_eq`). Consequently `Ω_c` is the skew
product of `(c + R_K) ds ∧ dt` and `ω` along `X_K`
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerGraphForm_eq_skewProd`), and it tames `J_K` wherever
`c + R_K > 0` and `ω` tames `J`
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerGraphForm_floerGraphAlmostComplex_pos`). On a graph,
`Ω_c(∂_s Γ_u, ∂_t Γ_u)` is the Floer energy density of `u` plus `c + R_K`
(`TauCeti.SmoothTwoForm.IsNondegenerate.floerGraphForm_graph`). On a domain of finite area with
bounded curvature, a large constant `c` therefore makes the `Ω_c`-energy of the graph the Floer
energy plus a bounded term. This is how compactness for unperturbed pseudoholomorphic curves in
`(ℝ × ℝ) × M` applies to solutions of the inhomogeneous Floer equation in `M`.

These are statements about one tangent space at a time, for the Floer data `(J, K)` of the
manifold Floer equation of `TauCeti.Geometry.Symplectic.Floer.Manifold`. The smoothness of `J_K` as
a section of the endomorphism bundle, and the closedness of `Ω_c`, are not treated here. For
bundled finite-regularity data with an antilinear forcing term, the same skew product is
`TauCeti.InhomogeneousTerm.graphStructureAt`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  graph construction, its taming form and the energy of graphs.
-/

public noncomputable section

open Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The Hamiltonian vector field `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}` of the perturbation one-form
`K = K_s ds + K_t dt` with manifold target, at the domain point `z` and the target point `x`: it
sends a tangent vector `(a, b)` of the domain to `a X_{K_s}(x) + b X_{K_t}(x)` in `T_x M`. -/
def hamiltonianOneForm (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ) (x : M) :
    ℝ × ℝ →L[ℝ] TangentSpace I x :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Ks z) x) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Kt z) x)

@[simp]
theorem hamiltonianOneForm_apply (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (z : ℝ × ℝ)
    (x : M) (v : ℝ × ℝ) :
    ω.hamiltonianOneForm Ks Kt z x v =
      v.1 • ω.hamiltonianVectorField (Ks z) x + v.2 • ω.hamiltonianVectorField (Kt z) x :=
  (rfl)

/-- The perturbed derivative is `du - X_K(u)`. -/
theorem perturbedMFDeriv_eq_sub (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z =
      -- As in `perturbedMFDeriv`, the difference is taken in maps out of the model `ℝ × ℝ`.
      HSub.hSub (α := ℝ × ℝ →L[ℝ] TangentSpace I (u z)) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z)
        (ω.hamiltonianOneForm Ks Kt z (u z)) :=
  ContinuousLinearMap.ext fun v ↦ (perturbedMFDeriv_apply ω Ks Kt u z v).trans (sub_sub _ _ _)

/-- The perturbed derivative is `du - X_K(u)`, applied to a tangent vector of the domain. -/
theorem perturbedMFDeriv_apply_eq_sub (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z v : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z v =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v - ω.hamiltonianOneForm Ks Kt z (u z) v :=
  (perturbedMFDeriv_apply ω Ks Kt u z v).trans (sub_sub _ _ _)

section AlmostComplex

variable (ω : SmoothTwoForm I M) (J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x))
  (Ks Kt : ℝ × ℝ → M → ℝ)

/-- **Gromov's almost complex structure** of the Floer equation on the tangent space
`(ℝ × ℝ) × T_x M` of `(ℝ × ℝ) × M` at `p = (z, x)`: the skew product of the standard structure `j`
of `ℝ × ℝ` and `J(z, x)` along the Hamiltonian one-form `X_K(z, x)`, so it sends `(ξ, v)` to
`(j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`. -/
def floerGraphAlmostComplex (p : (ℝ × ℝ) × M) :
    AlmostComplexStructure ((ℝ × ℝ) × TangentSpace I p.2) :=
  (AlmostComplexStructure.product ℝ).skewProd (J p.1 p.2)
    (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] TangentSpace I p.2)

theorem floerGraphAlmostComplex_def (p : (ℝ × ℝ) × M) :
    ω.floerGraphAlmostComplex J Ks Kt p =
      (AlmostComplexStructure.product ℝ).skewProd (J p.1 p.2)
        (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] TangentSpace I p.2) :=
  (rfl)

@[simp]
theorem floerGraphAlmostComplex_apply (p : (ℝ × ℝ) × M) (ζ : (ℝ × ℝ) × TangentSpace I p.2) :
    ω.floerGraphAlmostComplex J Ks Kt p ζ =
      (AlmostComplexStructure.product ℝ ζ.1,
        J p.1 p.2 (ζ.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ.1) +
          ω.hamiltonianOneForm Ks Kt p.1 p.2 (AlmostComplexStructure.product ℝ ζ.1)) := by
  simp [floerGraphAlmostComplex_def]

variable {ω J Ks Kt}

/-- **Gromov's graph construction in a manifold.** A map `u : ℝ × ℝ → M` solves the Floer
equation `(du - X_K)^{0,1} = 0` at `z` exactly when its graph `w ↦ (w, u w)` has a manifold
derivative at `z` which is complex linear from the standard structure of `ℝ × ℝ` to Gromov's
structure `J_K`. -/
theorem exists_hasMFDerivAt_graph_isComplexLinearMap_iff {u : ℝ × ℝ → M} {z : ℝ × ℝ} :
    (∃ Γ' : ℝ × ℝ →L[ℝ] (ℝ × ℝ) × TangentSpace I (u z),
        HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) (fun w ↦ (w, u w)) z Γ' ∧
          IsComplexLinearMap (AlmostComplexStructure.product ℝ)
            (ω.floerGraphAlmostComplex J Ks Kt (z, u z)) (Γ' : ℝ × ℝ →ₗ[ℝ] _)) ↔
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
          (ω.perturbedMFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] TangentSpace I (u z)) := by
  -- The derivative of `u`, read as a map out of the model space `ℝ × ℝ` of the domain.
  set du : ℝ × ℝ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z
  have hgraph (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
      HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) (fun w ↦ (w, u w)) z
        ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod du) :=
    (hasMFDerivAt_id z).prodMk hu.hasMFDerivAt
  have hlin : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (ω.floerGraphAlmostComplex J Ks Kt (z, u z))
        ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod du :
          ℝ × ℝ →ₗ[ℝ] (ℝ × ℝ) × TangentSpace I (u z)) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] TangentSpace I (u z)) := by
    rw [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id, floerGraphAlmostComplex_def,
      AlmostComplexStructure.isComplexLinearMap_id_prod_skewProd_iff,
      ← ContinuousLinearMap.toLinearMap_sub, perturbedMFDeriv_eq_sub]
  constructor
  · rintro ⟨Γ', hΓ', hΓ'lin⟩
    -- `u` is the second component of its graph.
    have hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
      mdifferentiableAt_snd.comp z hΓ'.mdifferentiableAt
    rw [hΓ'.mfderiv.symm.trans (hgraph hu).mfderiv] at hΓ'lin
    exact ⟨hu, hlin.mp hΓ'lin⟩
  · rintro ⟨hu, hulin⟩
    exact ⟨_, hgraph hu, hlin.mpr hulin⟩

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {j' : (y : N) → AlmostComplexStructure (TangentSpace I' y)}

/-- The projection to `ℝ × ℝ` of a map whose manifold derivative is complex linear into Gromov's
structure has a manifold derivative which is complex linear into the standard structure of
`ℝ × ℝ`. -/
theorem exists_hasMFDerivAt_fst_isComplexLinearMap {f : N → (ℝ × ℝ) × M} {y : N}
    {f' : TangentSpace I' y →L[ℝ] (ℝ × ℝ) × TangentSpace I (f y).2}
    (hf : HasMFDerivAt I' (𝓘(ℝ, ℝ × ℝ).prod I) f y f')
    (hlin : IsComplexLinearMap (j' y) (ω.floerGraphAlmostComplex J Ks Kt (f y))
      (f' : TangentSpace I' y →ₗ[ℝ] (ℝ × ℝ) × TangentSpace I (f y).2)) :
    ∃ f₁' : TangentSpace I' y →L[ℝ] ℝ × ℝ,
      HasMFDerivAt I' 𝓘(ℝ, ℝ × ℝ) (fun y ↦ (f y).1) y f₁' ∧
        IsComplexLinearMap (j' y) (AlmostComplexStructure.product ℝ)
          (f₁' : TangentSpace I' y →ₗ[ℝ] ℝ × ℝ) := by
  rw [floerGraphAlmostComplex_def, AlmostComplexStructure.isComplexLinearMap_skewProd_iff] at hlin
  exact ⟨(ContinuousLinearMap.fst ℝ (ℝ × ℝ) (TangentSpace I (f y).2)).comp f',
    (hasMFDerivAt_fst (f y)).comp y hf, hlin.1⟩

/-- **Vertical maps.** A map `y ↦ (z, g y)` into the fibre over a fixed domain point `z` has a
manifold derivative complex linear into Gromov's structure `J_K` exactly when `g` has a manifold
derivative complex linear into the structure `J(z, ·)` frozen at `z`. -/
theorem exists_hasMFDerivAt_prodMk_isComplexLinearMap_iff {g : N → M} {z : ℝ × ℝ} {y : N} :
    (∃ f' : TangentSpace I' y →L[ℝ] (ℝ × ℝ) × TangentSpace I (g y),
        HasMFDerivAt I' (𝓘(ℝ, ℝ × ℝ).prod I) (fun y ↦ (z, g y)) y f' ∧
          IsComplexLinearMap (j' y) (ω.floerGraphAlmostComplex J Ks Kt (z, g y))
            (f' : TangentSpace I' y →ₗ[ℝ] _)) ↔
      ∃ g' : TangentSpace I' y →L[ℝ] TangentSpace I (g y),
        HasMFDerivAt I' I g y g' ∧
          IsComplexLinearMap (j' y) (J z (g y)) (g' : TangentSpace I' y →ₗ[ℝ] _) := by
  have hvert {g' : TangentSpace I' y →L[ℝ] TangentSpace I (g y)} (hg : HasMFDerivAt I' I g y g') :
      HasMFDerivAt I' (𝓘(ℝ, ℝ × ℝ).prod I) (fun y ↦ (z, g y)) y
        ((0 : TangentSpace I' y →L[ℝ] ℝ × ℝ).prod g') :=
    (hasMFDerivAt_const z y).prodMk hg
  have hlin (g' : TangentSpace I' y →L[ℝ] TangentSpace I (g y)) :
      IsComplexLinearMap (j' y) (ω.floerGraphAlmostComplex J Ks Kt (z, g y))
          ((0 : TangentSpace I' y →L[ℝ] ℝ × ℝ).prod g' :
            TangentSpace I' y →ₗ[ℝ] (ℝ × ℝ) × TangentSpace I (g y)) ↔
        IsComplexLinearMap (j' y) (J z (g y)) (g' : TangentSpace I' y →ₗ[ℝ] _) := by
    rw [floerGraphAlmostComplex_def, AlmostComplexStructure.isComplexLinearMap_skewProd_iff,
      ContinuousLinearMap.coe_prod, LinearMap.fst_prod, LinearMap.snd_prod,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, sub_zero]
    exact and_iff_right (isComplexLinearMap_zero _ _)
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    -- `g` is the second component of the vertical map.
    have hg : HasMFDerivAt I' I g y ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) _).comp f') :=
      (hasMFDerivAt_snd (z, g y)).comp y hf'
    rw [hf'.mfderiv.symm.trans (hvert hg).mfderiv] at hf'lin
    exact ⟨_, hg, (hlin _).mp hf'lin⟩
  · rintro ⟨g', hg', hglin⟩
    exact ⟨_, hvert hg', (hlin g').mpr hglin⟩

end AlmostComplex

section TamingForm

/-- **Gromov's taming form** `Ω_c = pr₂^* ω + dK + c ds ∧ dt` on `(ℝ × ℝ) × M`, evaluated at the
point `p = (z, x)` on the tangent vectors `ζ = (ξ, v)` and `ζ' = (ξ', v')`. Here `dK` is the
exterior derivative of the one-form `K_s ds + K_t dt` on the product,
`dK_s(ζ) ds(ζ') + dK_t(ζ) dt(ζ') - dK_s(ζ') ds(ζ) - dK_t(ζ') dt(ζ)`, where the differential
`dK(ξ, v) = ∂_z K(z, x) ξ + d_x K(z, x) v` is the sum of the partial derivatives of `K` in the
domain and in the target. Where `K` is differentiable on the product manifold this is its derivative
there (`MDifferentiableAt.mvfderiv_prod_eq_add_apply`). -/
def floerGraphForm (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (c : ℝ) (p : (ℝ × ℝ) × M)
    (ζ ζ' : (ℝ × ℝ) × TangentSpace I p.2) : ℝ :=
  SmoothBundleForm.eval₂ ω p.2 ζ.2 ζ'.2 +
    ((fderiv ℝ (fun w ↦ Ks w p.2) p.1 ζ.1 + mvfderiv I (Ks p.1) p.2 ζ.2) * ζ'.1.1 +
        (fderiv ℝ (fun w ↦ Kt w p.2) p.1 ζ.1 + mvfderiv I (Kt p.1) p.2 ζ.2) * ζ'.1.2 -
      ((fderiv ℝ (fun w ↦ Ks w p.2) p.1 ζ'.1 + mvfderiv I (Ks p.1) p.2 ζ'.2) * ζ.1.1 +
        (fderiv ℝ (fun w ↦ Kt w p.2) p.1 ζ'.1 + mvfderiv I (Kt p.1) p.2 ζ'.2) * ζ.1.2)) +
    c * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1)

theorem floerGraphForm_def (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ) (c : ℝ)
    (p : (ℝ × ℝ) × M) (ζ ζ' : (ℝ × ℝ) × TangentSpace I p.2) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      SmoothBundleForm.eval₂ ω p.2 ζ.2 ζ'.2 +
        ((fderiv ℝ (fun w ↦ Ks w p.2) p.1 ζ.1 + mvfderiv I (Ks p.1) p.2 ζ.2) * ζ'.1.1 +
            (fderiv ℝ (fun w ↦ Kt w p.2) p.1 ζ.1 + mvfderiv I (Kt p.1) p.2 ζ.2) * ζ'.1.2 -
          ((fderiv ℝ (fun w ↦ Ks w p.2) p.1 ζ'.1 + mvfderiv I (Ks p.1) p.2 ζ'.2) * ζ.1.1 +
            (fderiv ℝ (fun w ↦ Kt w p.2) p.1 ζ'.1 + mvfderiv I (Kt p.1) p.2 ζ'.2) * ζ.1.2)) +
        c * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1) :=
  (rfl)

namespace IsNondegenerate

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
  {Ks Kt : ℝ × ℝ → M → ℝ} {p : (ℝ × ℝ) × M}
include hω

/-- The differential of a perturbation component on the product, in terms of its domain
derivatives in the two coordinate directions and the contraction of its Hamiltonian vector
field. -/
private theorem fderiv_add_mvfderiv_apply (K : ℝ × ℝ → M → ℝ)
    (ζ : (ℝ × ℝ) × TangentSpace I p.2) :
    fderiv ℝ (fun w ↦ K w p.2) p.1 ζ.1 + mvfderiv I (K p.1) p.2 ζ.2 =
      ζ.1.1 * fderiv ℝ (fun w ↦ K w p.2) p.1 stdComplexLineReal +
        ζ.1.2 * fderiv ℝ (fun w ↦ K w p.2) p.1 stdComplexLineImag +
          SmoothBundleForm.eval₂ ω p.2 (ω.hamiltonianVectorField (K p.1) p.2) ζ.2 := by
  have hcoord := (fderiv ℝ (fun w ↦ K w p.2) p.1 : (ℝ × ℝ) →ₗ[ℝ] ℝ).apply_stdComplexLine ζ.1
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hcoord
  rw [hcoord, hω.eval₂_hamiltonianVectorField]

/-- **The curvature identity for Gromov's taming form.** At `p = (z, x)`, the form
`Ω_c = pr₂^* ω + dK + c ds ∧ dt` evaluates to `ω(v - X_K ξ, v' - X_K ξ')` plus `c + R_K(z, x)`
times `(ds ∧ dt)(ξ, ξ')`, on tangent vectors `(ξ, v)` and `(ξ', v')`. -/
theorem floerGraphForm_eq (c : ℝ) (ζ ζ' : (ℝ × ℝ) × TangentSpace I p.2) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      SmoothBundleForm.eval₂ ω p.2 (ζ.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ.1)
          (ζ'.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ'.1) +
        (c + ω.hamiltonianCurvature Ks Kt p.1 p.2) * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1) := by
  rw [floerGraphForm_def, fderiv_add_mvfderiv_apply hω Ks, fderiv_add_mvfderiv_apply hω Ks,
    fderiv_add_mvfderiv_apply hω Kt, fderiv_add_mvfderiv_apply hω Kt, hamiltonianCurvature_def,
    poissonBracket_def]
  simp only [← hω.symplecticFormAt_apply, hamiltonianOneForm_apply]
  exact ((hω.symplecticFormAt p.2).apply_sub_smul_add_smul_add_mul _ _ _ _ _ _ _ _ _ _ _).symm

/-- Where `c + R_K ≠ 0`, Gromov's taming form at `p = (z, x)` is the skew product of
`(c + R_K(z, x)) ds ∧ dt` and `ω` along the Hamiltonian one-form `X_K(z, x)`. -/
theorem floerGraphForm_eq_skewProd {c : ℝ}
    (hc : c + ω.hamiltonianCurvature Ks Kt p.1 p.2 ≠ 0) (ζ ζ' : (ℝ × ℝ) × TangentSpace I p.2) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      ((stdSymplecticForm (V := ℝ)).rescale _ hc).skewProd (hω.symplecticFormAt p.2)
        (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] TangentSpace I p.2) ζ ζ' := by
  rw [floerGraphForm_eq hω, SymplecticForm.skewProd_apply, SymplecticForm.rescale_apply,
    stdSymplecticForm_apply, hω.symplecticFormAt_apply]
  simp only [ContinuousLinearMap.coe_coe, Real.inner_apply]
  ring

/-- **Gromov's taming form tames Gromov's almost complex structure** at every point
`p = (z, x)` where `ω` tames `J(z, x)` and `c + R_K(z, x) > 0`. -/
theorem floerGraphForm_floerGraphAlmostComplex_pos
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : (hω.symplecticFormAt p.2).Tames (J p.1 p.2)) {c : ℝ}
    (hc : 0 < c + ω.hamiltonianCurvature Ks Kt p.1 p.2) {ζ : (ℝ × ℝ) × TangentSpace I p.2}
    (hζ : ζ ≠ 0) :
    0 < ω.floerGraphForm Ks Kt c p ζ (ω.floerGraphAlmostComplex J Ks Kt p ζ) := by
  rw [floerGraphForm_eq_skewProd hω hc.ne', floerGraphAlmostComplex_def]
  exact SymplecticForm.skewProd_tames (stdSymplecticForm_tames_product.rescale_of_pos hc) hJ _ ζ hζ

/-- **The energy of a graph.** On the coordinate derivatives `∂_s Γ_u = (1, ∂_s u)` and
`∂_t Γ_u = (i, ∂_t u)` of the graph `Γ_u(w) = (w, u w)`, Gromov's taming form evaluates to the Floer
energy density of `u` plus `c + R_K(z, u z)`. -/
theorem floerGraphForm_graph (u : ℝ × ℝ → M) (z : ℝ × ℝ) (c : ℝ) :
    ω.floerGraphForm Ks Kt c (z, u z)
        (stdComplexLineReal, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (stdComplexLineImag, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) =
      ω.floerEnergyDensity Ks Kt u z + (c + ω.hamiltonianCurvature Ks Kt z (u z)) := by
  rw [floerGraphForm_eq hω, floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag]
  simp [stdComplexLineReal, stdComplexLineImag]

end IsNondegenerate

end TamingForm

end TauCeti.SmoothTwoForm
