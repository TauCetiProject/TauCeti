/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.JHolomorphic.Varying
public import TauCeti.Geometry.Symplectic.Prod.Skew
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.Geometry.Symplectic.StandardCompatible
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.WithLp

/-!
# Gromov's graph construction for the inhomogeneous Floer equation

Let `(V, ω)` be a symplectic vector space, `J` a family of almost complex structures on `V`
depending on a domain point `z = (s, t)` and a target point `x`, and `K = K_s ds + K_t dt` a
Hamiltonian perturbation. Write `X_K = ds ⊗ X_{K_s} + dt ⊗ X_{K_t}`
(`TauCeti.SymplecticForm.hamiltonianOneForm`) and `j` for the standard complex structure on
`ℝ × ℝ`. Following Gromov, put on `(ℝ × ℝ) × V` the almost complex structure

`J_K(z, x)(ξ, v) = (j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`,

the skew product of `j` and `J(z, x)` along `X_K(z, x)`
(`TauCeti.SymplecticForm.floerGraphAlmostComplex`). Then:

* a map `u` solves the Floer equation `(du - X_K)^{0,1} = 0` at `z` exactly when its graph
  `w ↦ (w, u w)` is `J_K`-holomorphic at `z`
  (`TauCeti.SymplecticForm.isJHolomorphicAt_graph_floerGraphAlmostComplex_iff`);
* the projection of a `J_K`-holomorphic map to `ℝ × ℝ` is `j`-holomorphic
  (`TauCeti.IsJHolomorphicAt.fst_of_floerGraphAlmostComplex`), and a map into a
  single fibre `{z} × V` is `J_K`-holomorphic exactly when it is holomorphic for the frozen
  structure `J(z, ·)`
  (`TauCeti.SymplecticForm.isJHolomorphicAt_prodMk_floerGraphAlmostComplex_iff`).

Thus solutions of the inhomogeneous equation become pseudoholomorphic curves of a product, and
the vertical maps, those lying in one fibre, are the pseudoholomorphic spheres for `J` frozen at a
domain point.

The same structure in complex coordinates `z = s + i t ∈ ℂ`, for a structure `J(z, x)` and a
one-form `X(z, x) : ℂ →L[ℝ] V` that need not come from a symplectic form, is
`J' = TauCeti.Floer.graphStructure J X`, a continuous-linear-map-valued function on the Euclidean
product `WithLp 2 (ℂ × V)` sending `(ξ, v)` to `(i ξ, J(z, x)(v - X(z, x) ξ) + X(z, x)(i ξ))`. This
is the form consumed by the local compactness theory of pseudoholomorphic curves. It squares to
`-1` wherever `J` does (`TauCeti.Floer.graphStructure_graphStructure`), is as regular as `J` and
`X` (`TauCeti.Floer.contDiffOn_graphStructure`), and `u` solves
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)` at `y` exactly when its graph `U` solves
`∂ₜU = J'(U) ∂ₛU` there (`TauCeti.Floer.fderiv_toLp_prodMk_I_eq_graphStructure_iff`).

For a constant `c`, consider the two-form `Ω_c = pr₂^* ω + dK + c ds ∧ dt` on `(ℝ × ℝ) × V`, where
`K` is read as the one-form `K_s ds + K_t dt` on the product
(`TauCeti.Floer.perturbationOneForm`) and `dK` is its exterior derivative. Since `dK` is
exact and the other two terms are constant, `Ω_c` is closed (for `C²` perturbations,
`d(dK) = 0` by `extDeriv_extDeriv` and `TauCeti.Floer.contDiff_perturbationOneForm`). Its values
are recorded by `TauCeti.SymplecticForm.floerGraphForm`, and the curvature `R_K` of
`TauCeti.Geometry.Symplectic.Floer.Energy` measures how far it is from a split form:

`Ω_c((ξ, v), (ξ', v')) = ω(v - X_K ξ, v' - X_K ξ') + (c + R_K) (ds ∧ dt)(ξ, ξ')`

(`TauCeti.SymplecticForm.floerGraphForm_eq`). Consequently `Ω_c` is the skew product of
`(c + R_K) ds ∧ dt` and `ω` along `X_K`, and it tames `J_K` wherever `c + R_K > 0` and `ω` tames
`J` (`TauCeti.SymplecticForm.floerGraphForm_floerGraphAlmostComplex_pos`). On a graph,
`Ω_c(∂_s Γ_u, ∂_t Γ_u)` is the Floer energy density plus `c + R_K`
(`TauCeti.SymplecticForm.floerGraphForm_graph`). On a domain of finite area and with bounded
curvature, a large constant `c` therefore makes the `Ω_c`-energy of the graph the Floer energy
plus a bounded term. This is how compactness for pseudoholomorphic curves applies to solutions
of the inhomogeneous Floer equation.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  graph construction, its taming form and the energy of graphs.
-/

public section

open Function

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section AlmostComplex

variable (ω : SymplecticForm V) (J : ℝ × ℝ → V → AlmostComplexStructure V)
  (Ks Kt : ℝ × ℝ → V → ℝ)

/-- **Gromov's almost complex structure** of the Floer equation on `(ℝ × ℝ) × V`: at the point
`p = (z, x)` it is the skew product of the standard structure `j` of `ℝ × ℝ` and `J(z, x)` along
the Hamiltonian one-form `X_K(z, x)`, so it sends `(ξ, v)` to
`(j ξ, J(z, x) (v - X_K ξ) + X_K (j ξ))`. -/
noncomputable def floerGraphAlmostComplex (p : (ℝ × ℝ) × V) :
    AlmostComplexStructure ((ℝ × ℝ) × V) :=
  (AlmostComplexStructure.product ℝ).skewProd (J p.1 p.2)
    (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] V)

theorem floerGraphAlmostComplex_def (p : (ℝ × ℝ) × V) :
    ω.floerGraphAlmostComplex J Ks Kt p =
      (AlmostComplexStructure.product ℝ).skewProd (J p.1 p.2)
        (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] V) :=
  (rfl)

@[simp]
theorem floerGraphAlmostComplex_apply (p ζ : (ℝ × ℝ) × V) :
    ω.floerGraphAlmostComplex J Ks Kt p ζ =
      (AlmostComplexStructure.product ℝ ζ.1,
        J p.1 p.2 (ζ.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ.1) +
          ω.hamiltonianOneForm Ks Kt p.1 p.2 (AlmostComplexStructure.product ℝ ζ.1)) := by
  simp [floerGraphAlmostComplex_def]

variable {ω J Ks Kt}

/-- **Gromov's graph construction.** A map `u` solves the Floer equation
`(du - X_K)^{0,1} = 0` at `z` exactly when its graph `w ↦ (w, u w)` is holomorphic at `z` from
the standard structure of `ℝ × ℝ` to Gromov's structure `J_K`. -/
theorem isJHolomorphicAt_graph_floerGraphAlmostComplex_iff {u : ℝ × ℝ → V} {z : ℝ × ℝ} :
    IsJHolomorphicAt (fun _ ↦ AlmostComplexStructure.product ℝ)
        (ω.floerGraphAlmostComplex J Ks Kt) (fun w ↦ (w, u w)) z ↔
      DifferentiableAt ℝ u z ∧
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
          (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) := by
  have hgraph (hu : DifferentiableAt ℝ u z) :
      HasFDerivAt (fun w ↦ (w, u w)) ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (fderiv ℝ u z)) z :=
    (hasFDerivAt_id z).prodMk hu.hasFDerivAt
  have hlin : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (ω.floerGraphAlmostComplex J Ks Kt (z, u z))
        ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (fderiv ℝ u z) : ℝ × ℝ →ₗ[ℝ] (ℝ × ℝ) × V) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) := by
    rw [ContinuousLinearMap.coe_prod, ContinuousLinearMap.coe_id, floerGraphAlmostComplex_def,
      AlmostComplexStructure.isComplexLinearMap_id_prod_skewProd_iff, perturbedFDeriv_eq_sub,
      ContinuousLinearMap.toLinearMap_sub]
  rw [isJHolomorphicAt_iff]
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    have hu : DifferentiableAt ℝ u z := hf'.differentiableAt.snd
    rw [hf'.unique (hgraph hu)] at hf'lin
    exact ⟨hu, hlin.mp hf'lin⟩
  · rintro ⟨hu, hulin⟩
    exact ⟨_, hgraph hu, hlin.mpr hulin⟩

/-- **Gromov's graph construction, globally.** A map `u` solves the Floer equation everywhere
exactly when its graph is `J_K`-holomorphic. -/
theorem isJHolomorphic_graph_floerGraphAlmostComplex_iff {u : ℝ × ℝ → V} :
    IsJHolomorphic (fun _ ↦ AlmostComplexStructure.product ℝ)
        (ω.floerGraphAlmostComplex J Ks Kt) (fun w ↦ (w, u w)) ↔
      Differentiable ℝ u ∧
        ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
          (ω.perturbedFDeriv Ks Kt u z : ℝ × ℝ →ₗ[ℝ] V) := by
  simp only [isJHolomorphic_iff, isJHolomorphicAt_graph_floerGraphAlmostComplex_iff]
  exact forall_and

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] {J' : U → AlmostComplexStructure U}

/-- The projection to `ℝ × ℝ` of a `J_K`-holomorphic map is holomorphic for the standard structure
of `ℝ × ℝ`. -/
theorem _root_.TauCeti.IsJHolomorphicAt.fst_of_floerGraphAlmostComplex {f : U → (ℝ × ℝ) × V}
    {y : U} (hf : IsJHolomorphicAt J' (ω.floerGraphAlmostComplex J Ks Kt) f y) :
    IsJHolomorphicAt J' (fun _ ↦ AlmostComplexStructure.product ℝ) (fun y ↦ (f y).1) y := by
  obtain ⟨f', hf', hlin⟩ := (isJHolomorphicAt_iff _ _ _ _).mp hf
  rw [floerGraphAlmostComplex_def, AlmostComplexStructure.isComplexLinearMap_skewProd_iff] at hlin
  refine isJHolomorphicAt_of_hasFDerivAt (hasFDerivAt_fst.comp y hf') ?_
  rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_fst]
  exact hlin.1

/-- **Vertical maps.** A map `y ↦ (z, g y)` into the fibre over a fixed domain point `z` is
`J_K`-holomorphic exactly when `g` is holomorphic for the structure `J(z, ·)` frozen at `z`. -/
theorem isJHolomorphicAt_prodMk_floerGraphAlmostComplex_iff {g : U → V} {z : ℝ × ℝ} {y : U} :
    IsJHolomorphicAt J' (ω.floerGraphAlmostComplex J Ks Kt) (fun y ↦ (z, g y)) y ↔
      IsJHolomorphicAt J' (J z) g y := by
  have hvert {g' : U →L[ℝ] V} (hg : HasFDerivAt g g' y) :
      HasFDerivAt (fun y ↦ (z, g y)) ((0 : U →L[ℝ] ℝ × ℝ).prod g') y :=
    (hasFDerivAt_const z y).prodMk hg
  have hlin (g' : U →L[ℝ] V) :
      IsComplexLinearMap (J' y) (ω.floerGraphAlmostComplex J Ks Kt (z, g y))
          ((0 : U →L[ℝ] ℝ × ℝ).prod g' : U →ₗ[ℝ] (ℝ × ℝ) × V) ↔
        IsComplexLinearMap (J' y) (J z (g y)) (g' : U →ₗ[ℝ] V) := by
    rw [floerGraphAlmostComplex_def, AlmostComplexStructure.isComplexLinearMap_skewProd_iff,
      ContinuousLinearMap.coe_prod, LinearMap.fst_prod, LinearMap.snd_prod,
      ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, sub_zero]
    exact and_iff_right (isComplexLinearMap_zero _ _)
  rw [isJHolomorphicAt_iff, isJHolomorphicAt_iff]
  constructor
  · rintro ⟨f', hf', hf'lin⟩
    have hg : DifferentiableAt ℝ g y := hf'.differentiableAt.snd
    rw [hf'.unique (hvert hg.hasFDerivAt)] at hf'lin
    exact ⟨_, hg.hasFDerivAt, (hlin _).mp hf'lin⟩
  · rintro ⟨g', hg', hglin⟩
    exact ⟨_, hvert hg', (hlin g').mpr hglin⟩

end AlmostComplex

end TauCeti.SymplecticForm

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]


/-- The perturbation `K = K_s ds + K_t dt` as a one-form on `(ℝ × ℝ) × V`: at `p = (z, x)` it
sends `(ξ, v)` to `K_s(z, x) ξ₁ + K_t(z, x) ξ₂`. -/
noncomputable def perturbationOneForm (Ks Kt : ℝ × ℝ → V → ℝ) (p : (ℝ × ℝ) × V) :
    ((ℝ × ℝ) × V) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ((ℝ × ℝ) × V) ℝ (0 : Fin 1)
    (Ks p.1 p.2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V) +
      Kt p.1 p.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V))

@[simp]
theorem perturbationOneForm_apply (Ks Kt : ℝ × ℝ → V → ℝ) (p : (ℝ × ℝ) × V)
    (ζ : Fin 1 → (ℝ × ℝ) × V) :
    perturbationOneForm Ks Kt p ζ = Ks p.1 p.2 * (ζ 0).1.1 + Kt p.1 p.2 * (ζ 0).1.2 := by
  simp [perturbationOneForm]

variable {Ks Kt : ℝ × ℝ → V → ℝ} {p : (ℝ × ℝ) × V}

/-- The perturbation one-form is the linear isometry `ContinuousAlternatingMap.ofSubsingletonLIE`
applied to the family of covectors `K_s ds + K_t dt`. -/
private theorem perturbationOneForm_eq :
    perturbationOneForm Ks Kt = fun q ↦
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := (ℝ × ℝ) × V) (F := ℝ) (0 : Fin 1)
        (uncurry Ks q • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V) +
          uncurry Kt q • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
            (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V)) := by
  funext ⟨z, x⟩
  simp [perturbationOneForm]

/-- The perturbation one-form is as smooth as its coefficients. In particular, for `C²`
coefficients `d(dK) = 0` by `extDeriv_extDeriv`. -/
theorem contDiff_perturbationOneForm {n : WithTop ℕ∞} (hKs : ContDiff ℝ n (uncurry Ks))
    (hKt : ContDiff ℝ n (uncurry Kt)) : ContDiff ℝ n (perturbationOneForm Ks Kt) := by
  rw [perturbationOneForm_eq]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := (ℝ × ℝ) × V) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp
      ((hKs.smul contDiff_const).add (hKt.smul contDiff_const))

/-- The exterior derivative of the perturbation one-form, in terms of the derivatives of `K_s`
and `K_t` on the product. -/
theorem extDeriv_perturbationOneForm_apply (hKs : DifferentiableAt ℝ (uncurry Ks) p)
    (hKt : DifferentiableAt ℝ (uncurry Kt) p) (ζ ζ' : (ℝ × ℝ) × V) :
    extDeriv (perturbationOneForm Ks Kt) p ![ζ, ζ'] =
      fderiv ℝ (uncurry Ks) p ζ * ζ'.1.1 + fderiv ℝ (uncurry Kt) p ζ * ζ'.1.2 -
        (fderiv ℝ (uncurry Ks) p ζ' * ζ.1.1 + fderiv ℝ (uncurry Kt) p ζ' * ζ.1.2) := by
  set L₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V)
  set L₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) V)
  set e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := (ℝ × ℝ) × V) (F := ℝ)
    (0 : Fin 1)
  have hderiv : HasFDerivAt (perturbationOneForm Ks Kt)
      ((e.toContinuousLinearEquiv : _ →L[ℝ] _).comp
        ((fderiv ℝ (uncurry Ks) p).smulRight L₁ + (fderiv ℝ (uncurry Kt) p).smulRight L₂)) p := by
    rw [perturbationOneForm_eq]
    exact e.toContinuousLinearEquiv.hasFDerivAt.comp p
      ((hKs.hasFDerivAt.smul_const L₁).add (hKt.hasFDerivAt.smul_const L₂))
  rw [extDeriv_apply_pair, hderiv.fderiv]
  simp [e, L₁, L₂]

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section TamingForm

variable {Ks Kt : ℝ × ℝ → V → ℝ} {p : (ℝ × ℝ) × V}

/-- **Gromov's taming form** `Ω_c = pr₂^* ω + dK + c ds ∧ dt` on `(ℝ × ℝ) × V`, evaluated at the
point `p` on the tangent vectors `ζ` and `ζ'`. Here `dK` is the exterior derivative of the
perturbation one-form `TauCeti.Floer.perturbationOneForm`. -/
noncomputable def floerGraphForm (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (c : ℝ)
    (p ζ ζ' : (ℝ × ℝ) × V) : ℝ :=
  ω ζ.2 ζ'.2 + extDeriv (perturbationOneForm Ks Kt) p ![ζ, ζ'] +
    c * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1)

omit [FiniteDimensional ℝ V] in
theorem floerGraphForm_def (ω : SymplecticForm V) (Ks Kt : ℝ × ℝ → V → ℝ) (c : ℝ)
    (p ζ ζ' : (ℝ × ℝ) × V) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      ω ζ.2 ζ'.2 + extDeriv (perturbationOneForm Ks Kt) p ![ζ, ζ'] +
        c * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1) :=
  (rfl)

/-- The derivative of a perturbation component on the product splits into its domain derivative
and the contraction of its Hamiltonian vector field. -/
private theorem fderiv_uncurry_apply (ω : SymplecticForm V) {K : ℝ × ℝ → V → ℝ}
    (hK : DifferentiableAt ℝ (uncurry K) p) (ζ : (ℝ × ℝ) × V) :
    fderiv ℝ (uncurry K) p ζ =
      ζ.1.1 * fderiv ℝ (fun w ↦ K w p.2) p.1 stdComplexLineReal +
        ζ.1.2 * fderiv ℝ (fun w ↦ K w p.2) p.1 stdComplexLineImag +
          ω (ω.hamiltonianVectorField (K p.1) p.2) ζ.2 := by
  obtain ⟨z, x⟩ := p
  obtain ⟨ξ, v⟩ := ζ
  have hleft : fderiv ℝ (fun w ↦ K w x) z ξ = fderiv ℝ (uncurry K) (z, x) (ξ, 0) :=
    congrArg (· ξ) (fderiv_slice_left hK)
  have hright : fderiv ℝ (K z) x v = fderiv ℝ (uncurry K) (z, x) (0, v) :=
    congrArg (· v) (fderiv_slice_right hK)
  have hsplit : fderiv ℝ (uncurry K) (z, x) (ξ, v) =
      fderiv ℝ (uncurry K) (z, x) (ξ, 0) + fderiv ℝ (uncurry K) (z, x) (0, v) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have hcoord := (fderiv ℝ (fun w ↦ K w x) z : (ℝ × ℝ) →ₗ[ℝ] ℝ).apply_stdComplexLine ξ
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hcoord
  rw [hsplit, ← hleft, ← hright, apply_hamiltonianVectorField, hcoord]

/-- **The curvature identity for Gromov's taming form.** At `p = (z, x)`, the form
`Ω_c = pr₂^* ω + dK + c ds ∧ dt` evaluates to `ω(v - X_K ξ, v' - X_K ξ')` plus `c + R_K(z, x)`
times `(ds ∧ dt)(ξ, ξ')`, on tangent vectors `(ξ, v)` and `(ξ', v')`. -/
theorem floerGraphForm_eq (ω : SymplecticForm V) (hKs : DifferentiableAt ℝ (uncurry Ks) p)
    (hKt : DifferentiableAt ℝ (uncurry Kt) p) (c : ℝ) (ζ ζ' : (ℝ × ℝ) × V) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      ω (ζ.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ.1)
          (ζ'.2 - ω.hamiltonianOneForm Ks Kt p.1 p.2 ζ'.1) +
        (c + ω.hamiltonianCurvature Ks Kt p.1 p.2) * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1) := by
  rw [floerGraphForm_def, extDeriv_perturbationOneForm_apply hKs hKt,
    fderiv_uncurry_apply ω hKs, fderiv_uncurry_apply ω hKs, fderiv_uncurry_apply ω hKt,
    fderiv_uncurry_apply ω hKt, hamiltonianCurvature_def, poissonBracket_def]
  simp only [hamiltonianOneForm_apply, map_sub, map_add, map_smul, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  set Xs := ω.hamiltonianVectorField (Ks p.1) p.2
  set Xt := ω.hamiltonianVectorField (Kt p.1) p.2
  have hXs : ω.toBilinForm Xs Xs = 0 := ω.self_eq_zero Xs
  have hXt : ω.toBilinForm Xt Xt = 0 := ω.self_eq_zero Xt
  have hXts : ω.toBilinForm Xt Xs = -ω.toBilinForm Xs Xt := (ω.neg_eq Xs Xt).symm
  have hv : ω.toBilinForm ζ.2 Xs = -ω.toBilinForm Xs ζ.2 := (ω.neg_eq Xs ζ.2).symm
  have hv' : ω.toBilinForm ζ.2 Xt = -ω.toBilinForm Xt ζ.2 := (ω.neg_eq Xt ζ.2).symm
  linear_combination ζ'.1.1 * hv + ζ'.1.2 * hv' - ζ.1.1 * ζ'.1.1 * hXs -
    ζ.1.2 * ζ'.1.2 * hXt - ζ.1.2 * ζ'.1.1 * hXts

/-- Where `c + R_K ≠ 0`, Gromov's taming form at `p = (z, x)` is the skew product of
`(c + R_K(z, x)) ds ∧ dt` and `ω` along the Hamiltonian one-form `X_K(z, x)`. -/
theorem floerGraphForm_eq_skewProd (ω : SymplecticForm V) (hKs : DifferentiableAt ℝ (uncurry Ks) p)
    (hKt : DifferentiableAt ℝ (uncurry Kt) p) {c : ℝ}
    (hc : c + ω.hamiltonianCurvature Ks Kt p.1 p.2 ≠ 0) (ζ ζ' : (ℝ × ℝ) × V) :
    ω.floerGraphForm Ks Kt c p ζ ζ' =
      ((stdSymplecticForm (V := ℝ)).rescale _ hc).skewProd ω
        (ω.hamiltonianOneForm Ks Kt p.1 p.2 : ℝ × ℝ →ₗ[ℝ] V) ζ ζ' := by
  rw [floerGraphForm_eq ω hKs hKt, skewProd_apply, rescale_apply, stdSymplecticForm_apply]
  simp only [ContinuousLinearMap.coe_coe, Real.inner_apply]
  ring

/-- **Gromov's taming form tames Gromov's almost complex structure** at every point
`p = (z, x)` where `ω` tames `J(z, x)` and `c + R_K(z, x) > 0`. -/
theorem floerGraphForm_floerGraphAlmostComplex_pos (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} (hKs : DifferentiableAt ℝ (uncurry Ks) p)
    (hKt : DifferentiableAt ℝ (uncurry Kt) p) (hJ : ω.Tames (J p.1 p.2)) {c : ℝ}
    (hc : 0 < c + ω.hamiltonianCurvature Ks Kt p.1 p.2) {ζ : (ℝ × ℝ) × V} (hζ : ζ ≠ 0) :
    0 < ω.floerGraphForm Ks Kt c p ζ (ω.floerGraphAlmostComplex J Ks Kt p ζ) := by
  rw [floerGraphForm_eq_skewProd ω hKs hKt hc.ne', floerGraphAlmostComplex_def]
  exact skewProd_tames (stdSymplecticForm_tames_product.rescale_of_pos hc) hJ _ ζ hζ

/-- **The energy of a graph.** On the coordinate derivatives `∂_s Γ_u = (1, ∂_s u)` and
`∂_t Γ_u = (i, ∂_t u)` of the graph `Γ_u(w) = (w, u w)`, Gromov's taming form evaluates to the Floer
energy density of `u` plus `c + R_K(z, u z)`. -/
theorem floerGraphForm_graph (ω : SymplecticForm V) {u : ℝ × ℝ → V} {z : ℝ × ℝ}
    (hKs : DifferentiableAt ℝ (uncurry Ks) (z, u z))
    (hKt : DifferentiableAt ℝ (uncurry Kt) (z, u z)) (c : ℝ) :
    ω.floerGraphForm Ks Kt c (z, u z) (stdComplexLineReal, fderiv ℝ u z stdComplexLineReal)
        (stdComplexLineImag, fderiv ℝ u z stdComplexLineImag) =
      ω.floerEnergyDensity Ks Kt u z + (c + ω.hamiltonianCurvature Ks Kt z (u z)) := by
  rw [floerGraphForm_eq ω hKs hKt, floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag]
  simp [stdComplexLineReal, stdComplexLineImag]

end TamingForm

end TauCeti.SymplecticForm

namespace TauCeti.Floer

open Complex ContinuousLinearMap Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

section GraphStructure

variable (J : ℂ × V → V →L[ℝ] V) (X : ℂ × V → ℂ →L[ℝ] V)

/-- **Gromov's structure in Euclidean graph coordinates.** For a domain-dependent structure
`J(z, x)` on `V` and a Hamiltonian one-form `X(z, x) : ℂ →L[ℝ] V`, this is the matrix-valued
structure on `WithLp 2 (ℂ × V)` sending `(ξ, v)` at `p = (z, x)` to
`(i ξ, J(z, x)(v - X(z, x) ξ) + X(z, x)(i ξ))`. -/
noncomputable def graphStructure (p : WithLp 2 (ℂ × V)) :
    WithLp 2 (ℂ × V) →L[ℝ] WithLp 2 (ℂ × V) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).symm.toContinuousLinearMap ∘L
    (inl ℝ ℂ V ∘L ContinuousLinearMap.mul ℝ ℂ I ∘L fst ℝ ℂ V +
      inr ℝ ℂ V ∘L (J p.ofLp ∘L (snd ℝ ℂ V - X p.ofLp ∘L fst ℝ ℂ V) +
        X p.ofLp ∘L ContinuousLinearMap.mul ℝ ℂ I ∘L fst ℝ ℂ V)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ V).toContinuousLinearMap

@[simp]
theorem graphStructure_apply (p ζ : WithLp 2 (ℂ × V)) :
    graphStructure J X p ζ = WithLp.toLp 2 (I * ζ.fst,
      J p.ofLp (ζ.snd - X p.ofLp ζ.fst) + X p.ofLp (I * ζ.fst)) := by
  simp [graphStructure, WithLp.ext_iff]

variable {J X}

/-- Gromov's structure squares to `-1` wherever `J` does. -/
theorem graphStructure_graphStructure {p : WithLp 2 (ℂ × V)}
    (hJ : ∀ v, J p.ofLp (J p.ofLp v) = -v) (ζ : WithLp 2 (ℂ × V)) :
    graphStructure J X p (graphStructure J X p ζ) = -ζ := by
  rw [WithLp.ext_iff, Prod.ext_iff]
  simp [← mul_assoc, hJ, map_neg]

/-- Gromov's structure is as regular as the almost complex structure and the Hamiltonian
one-form. -/
theorem contDiffOn_graphStructure {n : WithTop ℕ∞} {W : Set (ℂ × V)}
    (hJ : ContDiffOn ℝ n J W) (hX : ContDiffOn ℝ n X W) :
    ContDiffOn ℝ n (graphStructure J X) (WithLp.ofLp ⁻¹' W) := by
  have hJ' : ContDiffOn ℝ n (fun p : WithLp 2 (ℂ × V) ↦ J p.ofLp) (WithLp.ofLp ⁻¹' W) :=
    hJ.comp WithLp.contDiff_ofLp.contDiffOn (mapsTo_preimage _ _)
  have hX' : ContDiffOn ℝ n (fun p : WithLp 2 (ℂ × V) ↦ X p.ofLp) (WithLp.ofLp ⁻¹' W) :=
    hX.comp WithLp.contDiff_ofLp.contDiffOn (mapsTo_preimage _ _)
  exact contDiffOn_const.clm_comp ((contDiffOn_const.add (contDiffOn_const.clm_comp
    ((hJ'.clm_comp (contDiffOn_const.sub (hX'.clm_comp contDiffOn_const))).add
      (hX'.clm_comp contDiffOn_const)))).clm_comp contDiffOn_const)

end GraphStructure

section EuclideanGraph

variable {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {u : ℂ → V} {y : ℂ}

/-- **Gromov's graph construction in Euclidean coordinates.** A map `u` differentiable at `y`
solves the inhomogeneous equation `∂ₜu - X(y, u) i = J(y, u)(∂ₛu - X(y, u) 1)` at `y` exactly when
its graph solves `∂ₜU = J'(U) ∂ₛU` there. -/
theorem fderiv_toLp_prodMk_I_eq_graphStructure_iff (hu : DifferentiableAt ℝ u y) :
    fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) y I =
        graphStructure J X (WithLp.toLp 2 (y, u y))
          (fderiv ℝ (fun w ↦ WithLp.toLp 2 (w, u w)) y 1) ↔
      fderiv ℝ u y I - X (y, u y) I = J (y, u y) (fderiv ℝ u y 1 - X (y, u y) 1) := by
  simp only [fderiv_toLp_prodMk_apply differentiableAt_fun_id hu, fderiv_fun_id,
    graphStructure_apply, WithLp.ext_iff, Prod.ext_iff, WithLp.toLp_fst, WithLp.toLp_snd,
    ContinuousLinearMap.id_apply, mul_one, true_and]
  exact sub_eq_iff_eq_add.symm

end EuclideanGraph

end TauCeti.Floer
