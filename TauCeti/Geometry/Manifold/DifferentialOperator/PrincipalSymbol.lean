/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.Geometry.Manifold.VectorField.Derivation
public import TauCeti.RingTheory.Derivation.PrincipalSymbol
import Mathlib.Data.Nat.Choose.Cast

/-!
# The principal symbol of a differential operator on smooth functions

Let `D` be a differential operator of order at most `m` on the smooth real functions of a
finite-dimensional Hausdorff manifold `M`, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`); no continuity of `D` is assumed. With
`[D, f] = D ∘ M_f - M_f ∘ D`, the `m`-fold commutator `[⋯[D, f₁], …, fₘ]` is multiplication by the
smooth function `[⋯[D, f₁], …, fₘ] 1`. At an interior point `x` its value depends only on the
differentials `(df₁)ₓ, …, (dfₘ)ₓ`, and is real-multilinear and symmetric in them. This gives the
**commutator symbol** of `D` at `x`,

`TauCeti.smoothCommutatorSymbol hx D : T_x*M × ⋯ × T_x*M → ℝ`,
`(df₁(x), …, dfₘ(x)) ↦ ([⋯[D, f₁], …, fₘ] 1)(x)` (`TauCeti.smoothCommutatorSymbol_mvfderiv`),

and the **principal symbol** of `D` at `x`, in the geometric convention without factors of `i`,

`TauCeti.smoothPrincipalSymbol I hx D ξ = (1 / m!) σ(ξ, …, ξ)`,

so that `σ_geom(D)(df_x) = (1 / m!) ([⋯[D, f], …, f] 1)(x)` with `m` copies of `f`
(`TauCeti.smoothPrincipalSymbol_mvfderiv`). The commutator symbol is `m!` times the polarization of
the principal symbol. For instance a derivation, that is differentiation along a vector field `X`,
has principal symbol `ξ ↦ ξ(X_x)`, and since principal symbols multiply under composition, its
square, such as the second derivative on `ℝ`, has principal symbol `ξ ↦ ξ(X_x)²`.
In the Fourier convention of pseudodifferential operators, where `∂ⱼ` has symbol `i ξⱼ`, the
principal symbol of an operator of order `m` is `i ^ m` times this one.

The commutator symbol at `x` is the cotangent symbol `TauCeti.cotangentSymbol` of the vanishing
ideal `I_x`, read through the identification `I_x / I_x² ≃ T_x*M`
(`TauCeti.smoothCotangentEquiv`) and evaluation at `x`
(`TauCeti.mk_algebraMap_smoothCommutatorSymbol`). Both rest on the same fact
(`TauCeti.commutatorSymbol_apply_sub_mem_smul_top`): modulo `I_x`, the iterated commutator only
depends on its entries modulo `I_x²`, and a function vanishing at `x` lies in `I_x²` exactly when
its differential at `x` vanishes (Hadamard's lemma).

The principal symbol is natural: transporting an operator along a diffeomorphism `φ : N → M`, by
conjugation with the pullback of functions, pulls its principal symbol back by the differential of
`φ` (`TauCeti.smoothPrincipalSymbol_conjDifferentialOperators`).

## Main definitions

* `TauCeti.smoothCommutatorSymbol I hx`: the commutator symbol at an interior point `x`, a real
  multilinear form on the cotangent space `T_x*M`, linear in the operator.
* `TauCeti.smoothPrincipalSymbol I hx D`: the principal symbol of `D` at `x`, a homogeneous
  function of degree `m` on `T_x*M`.

## Main results

* `TauCeti.smoothCommutatorSymbol_mvfderiv`, `TauCeti.smoothPrincipalSymbol_mvfderiv`: the values
  at differentials of functions are the iterated commutators.
* `TauCeti.smoothCommutatorSymbol_comp_perm`: the commutator symbol is symmetric.
* `TauCeti.mk_algebraMap_smoothCommutatorSymbol`: comparison with the cotangent symbol of the
  vanishing ideal.
* `TauCeti.smoothPrincipalSymbol_smul_covector`: the principal symbol is homogeneous of degree `m`.
* `TauCeti.smoothPrincipalSymbol_comp`: principal symbols multiply under composition.
* `TauCeti.smoothPrincipalSymbol_derivation_mvfderiv`: a derivation `δ` has principal symbol
  `df_x ↦ (δ f)(x)`.
* `TauCeti.smoothPrincipalSymbol_vectorFieldDerivation`, `TauCeti.smoothPrincipalSymbol_derivation`:
  differentiation along a vector field `X` has principal symbol `ξ ↦ ξ(X_x)`.
* `TauCeti.forall_smoothCommutatorSymbol_eq_zero_iff`: on a boundaryless manifold, an operator of
  order at most `m + 1` has vanishing commutator symbol at every point exactly when it has order at
  most `m`.
* `TauCeti.smoothCommutatorSymbol_conjDifferentialOperators`,
  `TauCeti.smoothPrincipalSymbol_conjDifferentialOperators`: naturality under diffeomorphisms.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {x : M}

/-! ### Lifting covectors to functions -/

/-- The differential at `x` of the functions vanishing at `x`, as a real-linear map. -/
private def vanishingIdealDifferential (hx : I.IsInteriorPoint x) :
    smoothVanishingIdeal I x →ₗ[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  (smoothCotangentEquiv hx).toLinearMap ∘ₗ
    ((smoothVanishingIdeal I x).toCotangent.restrictScalars ℝ)

private theorem vanishingIdealDifferential_apply (hx : I.IsInteriorPoint x)
    (f : smoothVanishingIdeal I x) :
    vanishingIdealDifferential hx f = mvfderiv I (f : C^∞⟮I, M; ℝ⟯) x :=
  smoothCotangentEquiv_toCotangent hx f

private theorem exists_vanishingIdealDifferential_comp_eq_id (hx : I.IsInteriorPoint x) :
    ∃ s : (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] smoothVanishingIdeal I x,
      vanishingIdealDifferential hx ∘ₗ s = LinearMap.id :=
  (vanishingIdealDifferential hx).exists_rightInverse_of_surjective <| LinearMap.range_eq_top.2 <|
    (smoothCotangentEquiv hx).surjective.comp (smoothVanishingIdeal I x).toCotangent_surjective

/-- A real-linear choice of a smooth function vanishing at `x` with prescribed differential at
`x`. -/
private def covectorLift (hx : I.IsInteriorPoint x) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  (smoothVanishingIdeal I x).subtype.restrictScalars ℝ ∘ₗ
    (exists_vanishingIdealDifferential_comp_eq_id hx).choose

private theorem covectorLift_apply_self (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : covectorLift hx ξ x = 0 :=
  mem_smoothVanishingIdeal_iff.mp ((exists_vanishingIdealDifferential_comp_eq_id hx).choose ξ).2

private theorem mvfderiv_covectorLift (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : mvfderiv I (covectorLift hx ξ) x = ξ := by
  have h := congr($((exists_vanishingIdealDifferential_comp_eq_id hx).choose_spec) ξ)
  rwa [LinearMap.comp_apply, vanishingIdealDifferential_apply] at h

/-! ### The commutator symbol -/

/-- Evaluation at `x` of the image of `1` under a linear map of smooth functions. -/
private def evalOneAt (x : M) : (C^∞⟮I, M; ℝ⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯) →ₗ[ℝ] ℝ where
  toFun L := L 1 x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (I) in
/-- The commutator symbol of a differential operator `D` of order at most `m` on smooth functions
at an interior point `x`: the real multilinear form on the cotangent space `T_x*M` sending
`(df₁(x), …, dfₘ(x))` to the value at `x` of the iterated commutator `[⋯[D, f₁], …, fₘ] 1`
(`TauCeti.smoothCommutatorSymbol_mvfderiv`). It is symmetric
(`TauCeti.smoothCommutatorSymbol_comp_perm`) and `m!` times the polarization of the principal
symbol `TauCeti.smoothPrincipalSymbol`. -/
def smoothCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ} :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin m ↦ TangentSpace I x →L[ℝ] ℝ) ℝ where
  toFun D := ((evalOneAt x).compMultilinearMap
      ((commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) D)).compLinearMap
    fun _ ↦ covectorLift hx
  map_add' D₁ D₂ := by ext; simp
  map_smul' c D := by ext; simp

/-- The commutator symbol at `x`, evaluated on the differentials at `x` of smooth functions
`f₁, …, fₘ`, is the value at `x` of the iterated commutator `[⋯[D, f₁], …, fₘ] 1`. -/
theorem smoothCommutatorSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : Fin m → C^∞⟮I, M; ℝ⟯) :
    smoothCommutatorSymbol I hx D (fun i ↦ mvfderiv I (f i) x) =
      commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m D f 1 x := by
  -- The lifts `gᵢ` of the differentials differ from `fᵢ - fᵢ(x)` by elements of `I_x²`.
  set g : Fin m → C^∞⟮I, M; ℝ⟯ := fun i ↦ covectorLift hx (mvfderiv I (f i) x)
  have hc (c : ℝ) : ⇑(algebraMap ℝ C^∞⟮I, M; ℝ⟯ c) = fun _ ↦ c := funext fun _ ↦ by simp
  have hd (h : C^∞⟮I, M; ℝ⟯) : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
    (h.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
  have hg : ∀ i, (fun i ↦ g i + algebraMap ℝ C^∞⟮I, M; ℝ⟯ (f i x)) i - f i ∈
      smoothVanishingIdeal I x ^ 2 := fun i ↦ by
    refine mem_smoothVanishingIdeal_sq_of_mvfderiv_eq_zero hx ?_ ?_
    · simp [g, hc, covectorLift_apply_self]
    · rw [ContMDiffMap.coe_sub, ContMDiffMap.coe_add, hc,
        mvfderiv_sub ((hd _).add mdifferentiableAt_const) (hd _), mvfderiv_add (hd _)
          mdifferentiableAt_const, mvfderiv_const, add_zero, mvfderiv_covectorLift, sub_self]
  have h := commutatorSymbol_apply_sub_mem_smul_top D hg 1
  rw [commutatorSymbol_add_algebraMap, smul_eq_mul, Ideal.mul_top, mem_smoothVanishingIdeal_iff,
    ContMDiffMap.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  exact h

/-- Every covector is the differential of a smooth function, so the commutator symbol is
determined by `TauCeti.smoothCommutatorSymbol_mvfderiv`. -/
private theorem exists_mvfderiv_eq (hx : I.IsInteriorPoint x) {m : ℕ}
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) :
    ∃ f : Fin m → C^∞⟮I, M; ℝ⟯, (fun i ↦ mvfderiv I (f i) x) = ξ :=
  ⟨fun i ↦ covectorLift hx (ξ i), funext fun i ↦ mvfderiv_covectorLift hx (ξ i)⟩

/-- The commutator symbol is symmetric. -/
theorem smoothCommutatorSymbol_comp_perm (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) (σ : Equiv.Perm (Fin m)) :
    smoothCommutatorSymbol I hx D (ξ ∘ σ) = smoothCommutatorSymbol I hx D ξ := by
  obtain ⟨f, rfl⟩ := exists_mvfderiv_eq hx ξ
  have h := smoothCommutatorSymbol_mvfderiv hx D (f ∘ σ)
  rwa [commutatorSymbol_comp_perm, ← smoothCommutatorSymbol_mvfderiv hx D f] at h

/-- **Comparison with the cotangent symbol.** The commutator symbol at `x` is the cotangent symbol
`TauCeti.cotangentSymbol` of the vanishing ideal `I_x`, read through the identification
`I_x / I_x² ≃ T_x*M` and evaluation at `x`: the class modulo `I_x` of the constant function with
value `σ(u₁, …, uₘ)` is the image of the class of `1` under the cotangent symbol at
`(u₁, …, uₘ)`. -/
theorem mk_algebraMap_smoothCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (u : Fin m → (smoothVanishingIdeal I x).Cotangent) :
    Submodule.Quotient.mk (p := (smoothVanishingIdeal I x • ⊤ : Submodule C^∞⟮I, M; ℝ⟯ _))
        (algebraMap ℝ C^∞⟮I, M; ℝ⟯
          (smoothCommutatorSymbol I hx D fun i ↦ smoothCotangentEquiv hx (u i))) =
      cotangentSymbol ℝ (smoothVanishingIdeal I x) D u (Submodule.Quotient.mk 1) := by
  choose a ha using fun i ↦ (smoothVanishingIdeal I x).toCotangent_surjective (u i)
  obtain rfl : (fun i ↦ (smoothVanishingIdeal I x).toCotangent (a i)) = u := funext ha
  simp only [smoothCotangentEquiv_toCotangent, cotangentSymbol_toCotangent]
  rw [smoothCommutatorSymbol_mvfderiv, Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top,
    mem_smoothVanishingIdeal_iff, ContMDiffMap.coe_sub, Pi.sub_apply,
    ContMDiffMap.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
/-- A linear map of the smooth functions over themselves is multiplication by the image of `1`. -/
private theorem linearMap_apply_apply_eq_mul (L : C^∞⟮I, M; ℝ⟯ →ₗ[C^∞⟮I, M; ℝ⟯] C^∞⟮I, M; ℝ⟯)
    (g : C^∞⟮I, M; ℝ⟯) : L g x = g x * L 1 x := by
  have h := L.map_smul g 1
  rw [smul_eq_mul, mul_one] at h
  rw [h, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply]

/-- On a boundaryless manifold, an operator of order at most `m + 1` has vanishing commutator
symbol at every point if and only if it has order at most `m`. -/
theorem forall_smoothCommutatorSymbol_eq_zero_iff [BoundarylessManifold I M] {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ (m + 1)) :
    (∀ x : M, smoothCommutatorSymbol I (BoundarylessManifold.isInteriorPoint (x := x)) D = 0) ↔
      (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m := by
  rw [← commutatorSymbol_eq_zero_iff]
  constructor
  · intro h
    -- The iterated commutators are linear over the smooth functions, so it suffices that their
    -- values at `1` vanish at every point.
    refine MultilinearMap.ext fun f ↦ LinearMap.ext_ring <| ContMDiffMap.ext fun y ↦ ?_
    rw [← smoothCommutatorSymbol_mvfderiv BoundarylessManifold.isInteriorPoint, h y]
    simp
  · intro h x
    ext ξ
    obtain ⟨f, rfl⟩ := exists_mvfderiv_eq BoundarylessManifold.isInteriorPoint ξ
    simp [smoothCommutatorSymbol_mvfderiv, h]

/-! ### The principal symbol -/

variable (I) in
/-- The principal symbol of a differential operator `D` of order at most `m` on smooth functions
at an interior point `x`, in the geometric convention: the homogeneous function of degree `m` on
the cotangent space `T_x*M` given by `σ_geom(D)(df_x) = (1 / m!) ([⋯[D, f], …, f] 1)(x)`, with `m`
copies of `f` (`TauCeti.smoothPrincipalSymbol_mvfderiv`). Its polarization is `1 / m!` times the
commutator symbol `TauCeti.smoothCommutatorSymbol`. -/
def smoothPrincipalSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : ℝ :=
  (m.factorial : ℝ)⁻¹ * smoothCommutatorSymbol I hx D fun _ ↦ ξ

theorem smoothPrincipalSymbol_def (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx D ξ =
      (m.factorial : ℝ)⁻¹ * smoothCommutatorSymbol I hx D fun _ ↦ ξ :=
  (rfl)

/-- The principal symbol at the differential of `f` is `1 / m!` times the value at `x` of the
`m`-fold commutator `[⋯[D, f], …, f] 1`. -/
theorem smoothPrincipalSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (f : C^∞⟮I, M; ℝ⟯) :
    smoothPrincipalSymbol I hx D (mvfderiv I f x) =
      (m.factorial : ℝ)⁻¹ * (smulCommutator ℝ f ^ m) (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) 1 x := by
  rw [smoothPrincipalSymbol_def, smoothCommutatorSymbol_mvfderiv hx D fun _ ↦ f,
    commutatorSymbol_const_apply]

@[simp]
theorem smoothPrincipalSymbol_zero (hx : I.IsInteriorPoint x) {m : ℕ}
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx
      (0 : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) ξ = 0 := by
  simp [smoothPrincipalSymbol_def]

@[simp]
theorem smoothPrincipalSymbol_add (hx : I.IsInteriorPoint x) {m : ℕ}
    (D₁ D₂ : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx (D₁ + D₂) ξ =
      smoothPrincipalSymbol I hx D₁ ξ + smoothPrincipalSymbol I hx D₂ ξ := by
  simp [smoothPrincipalSymbol_def, mul_add]

@[simp]
theorem smoothPrincipalSymbol_smul (hx : I.IsInteriorPoint x) {m : ℕ} (c : ℝ)
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx (c • D) ξ = c * smoothPrincipalSymbol I hx D ξ := by
  simp only [smoothPrincipalSymbol_def, map_smul, smul_apply, smul_eq_mul]
  ring

/-- The principal symbol of an operator of order at most `m` is homogeneous of degree `m`. -/
theorem smoothPrincipalSymbol_smul_covector (hx : I.IsInteriorPoint x) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m) (c : ℝ)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx D (c • ξ) = c ^ m * smoothPrincipalSymbol I hx D ξ := by
  have h := (smoothCommutatorSymbol I hx D).map_smul_univ (fun _ ↦ c) fun _ ↦ ξ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [smoothPrincipalSymbol_def, smoothPrincipalSymbol_def, h]
  ring

/-- **Principal symbols multiply under composition.** For operators `P` and `Q` of orders at most
`m` and `k`, the principal symbol of `P ∘ Q`, as an operator of order at most `m + k`, is the
product of the principal symbols. -/
theorem smoothPrincipalSymbol_comp (hx : I.IsInteriorPoint x) {m k : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx
        ⟨(P : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯) ∘ₗ (Q : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯),
          comp_mem_differentialOperators P.2 Q.2⟩ ξ =
      smoothPrincipalSymbol I hx P ξ * smoothPrincipalSymbol I hx Q ξ := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  -- The `(m + k)`-fold commutator of `P ∘ Q` with `f` is `(m + k).choose m` times the product of
  -- the commutators of `P` and `Q`, and `(m + k).choose m / (m + k)! = 1 / (m! k!)`.
  have key := congr($(commutatorSymbol_comp_const P Q f) 1 x)
  rw [LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℝ, ContMDiffMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, LinearMap.comp_apply, linearMap_apply_apply_eq_mul
      (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m P fun _ ↦ f)] at key
  simp only [smoothPrincipalSymbol_def]
  rw [smoothCommutatorSymbol_mvfderiv hx _ fun _ ↦ f,
    smoothCommutatorSymbol_mvfderiv hx P fun _ ↦ f, smoothCommutatorSymbol_mvfderiv hx Q fun _ ↦ f,
    key, Nat.cast_add_choose]
  field_simp

/-! ### Naturality under diffeomorphisms -/

section Diffeomorph

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

/-- **Naturality of the commutator symbol.** Transport the operator `D` on `M` to `N` along a
diffeomorphism `φ : N → M`, by conjugation with the pullback `f ↦ f ∘ φ`. Its commutator symbol
at `y` on the pullbacks `η ∘ dφ_y` of covectors at `φ y` is the commutator symbol of `D` at `φ y`
on the covectors `η`. -/
theorem smoothCommutatorSymbol_conjDifferentialOperators (φ : N ≃ₘ⟮J, I⟯ M) {y : N}
    (hy : J.IsInteriorPoint y) (hx : I.IsInteriorPoint (φ y)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (η : Fin m → TangentSpace I (φ y) →L[ℝ] ℝ) :
    smoothCommutatorSymbol J hy ((φ.compRightAlgEquiv ℝ ℝ).conjDifferentialOperators m D)
        (fun i ↦ (η i).comp (mfderiv J I φ y)) =
      smoothCommutatorSymbol I hx D η := by
  obtain ⟨f, rfl⟩ := exists_mvfderiv_eq hx η
  have hd (i : Fin m) : (mvfderiv I (f i) (φ y)).comp (mfderiv J I φ y) =
      mvfderiv J (φ.compRightAlgEquiv ℝ ℝ (f i)) y := by
    rw [Diffeomorph.coe_compRightAlgEquiv_apply]
    exact (mvfderiv_comp y ((f i).contMDiff.mdifferentiable (by simp) _)
      (φ.contMDiff.mdifferentiable (by simp) y)).symm
  simp only [hd]
  rw [smoothCommutatorSymbol_mvfderiv, smoothCommutatorSymbol_mvfderiv,
    commutatorSymbol_conjDifferentialOperators, map_one, Diffeomorph.compRightAlgEquiv_apply]

/-- **Naturality of the principal symbol.** The principal symbol at `y` of the transport of `D`
along a diffeomorphism `φ : N → M` is the principal symbol of `D` at `φ y`, the covectors being
pulled back by the differential `dφ_y`: `σ(φ^* D)_y(η ∘ dφ_y) = σ(D)_{φ y}(η)`. -/
theorem smoothPrincipalSymbol_conjDifferentialOperators (φ : N ≃ₘ⟮J, I⟯ M) {y : N}
    (hy : J.IsInteriorPoint y) (hx : I.IsInteriorPoint (φ y)) {m : ℕ}
    (D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m)
    (η : TangentSpace I (φ y) →L[ℝ] ℝ) :
    smoothPrincipalSymbol J hy ((φ.compRightAlgEquiv ℝ ℝ).conjDifferentialOperators m D)
        (η.comp (mfderiv J I φ y)) =
      smoothPrincipalSymbol I hx D η := by
  rw [smoothPrincipalSymbol_def, smoothPrincipalSymbol_def,
    smoothCommutatorSymbol_conjDifferentialOperators φ hy hx D fun _ ↦ η]

end Diffeomorph

/-! ### Derivations -/

/-- The principal symbol of a derivation `δ` at `df_x` is `(δ f)(x)`. -/
theorem smoothPrincipalSymbol_derivation_mvfderiv (hx : I.IsInteriorPoint x)
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (f : C^∞⟮I, M; ℝ⟯) :
    smoothPrincipalSymbol I hx ⟨δ, δ.mem_differentialOperators_one⟩ (mvfderiv I f x) = δ f x := by
  rw [smoothPrincipalSymbol_def, Nat.factorial_one, Nat.cast_one, inv_one, one_mul,
    smoothCommutatorSymbol_mvfderiv hx _ fun _ ↦ f, ← Matrix.vec_single_eq_const f,
    Derivation.commutatorSymbol_derivation, one_smul]

/-- Differentiation along a smooth vector field `X` has principal symbol `ξ ↦ ξ(X_x)`. -/
@[simp]
theorem smoothPrincipalSymbol_vectorFieldDerivation (hx : I.IsInteriorPoint x)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I hx ⟨vectorFieldDerivation X,
      (vectorFieldDerivation X).mem_differentialOperators_one⟩ ξ = ξ (X x) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  rw [smoothPrincipalSymbol_derivation_mvfderiv, ContMDiffSection.vectorFieldDerivation_apply_apply]

/-- On a boundaryless manifold, a derivation `δ` of the smooth functions has principal symbol
`ξ ↦ ξ(X_x)`, where `X = δ.vectorField` is its vector field. -/
@[simp]
theorem smoothPrincipalSymbol_derivation [BoundarylessManifold I M]
    (δ : Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothPrincipalSymbol I BoundarylessManifold.isInteriorPoint
      ⟨δ, δ.mem_differentialOperators_one⟩ ξ = ξ (δ.vectorField x) := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ :=
    ⟨_, mvfderiv_covectorLift BoundarylessManifold.isInteriorPoint ξ⟩
  rw [smoothPrincipalSymbol_derivation_mvfderiv, Derivation.mvfderiv_vectorField]

end TauCeti
