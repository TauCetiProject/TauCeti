/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# The principal symbol of a differential operator between vector bundles

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff manifold `M`,
with `V` of finite rank, and let `P : Γ(V) → Γ(W)` be a differential operator of order at most
`m` between their smooth sections, in Grothendieck's sense of iterated commutators with
multiplication operators (`TauCeti.differentialOperators`); no continuity of `P` is assumed.
With `[P, f] = P ∘ M_f - M_f ∘ P`, the `m`-fold commutator `[⋯[P, f₁], …, fₘ]` is linear over the
smooth functions, so its value `([⋯[P, f₁], …, fₘ] s)(x)` depends only on `s(x)`
(`TauCeti.smoothSectionFiberMap`). At an interior point `x` it also depends only on the
differentials `(df₁)ₓ, …, (dfₘ)ₓ`, and is real-multilinear and symmetric in them. This gives the
**commutator symbol** of `P` at `x`,

`TauCeti.sectionCommutatorSymbol I hx P : T_x*M × ⋯ × T_x*M → Hom(V_x, W_x)`,
`(df₁(x), …, dfₘ(x)) ↦ (s(x) ↦ ([⋯[P, f₁], …, fₘ] s)(x))`
(`TauCeti.sectionCommutatorSymbol_mvfderiv`),

and the **principal symbol** of `P` at `x`, in the geometric convention without factors of `i`,

`TauCeti.sectionPrincipalSymbol I hx P ξ = (1 / m!) σ(ξ, …, ξ) : V_x → W_x`,

so that `σ_geom(P)(df_x) s(x) = (1 / m!) ([⋯[P, f], …, f] s)(x)` with `m` copies of `f`
(`TauCeti.sectionPrincipalSymbol_mvfderiv`). This is the vector bundle version of
`TauCeti.smoothPrincipalSymbol`, which treats operators on the smooth functions. In the Fourier
convention of pseudodifferential operators, where `∂ⱼ` has symbol `i ξⱼ`, the principal symbol of
an operator of order `m` is `i ^ m` times this one.

The principal symbol is homogeneous of degree `m` in the covector, vanishes on operators of lower
order, and is multiplicative: `σ(P ∘ Q) = σ(P) ∘ σ(Q)` when the intermediate bundle `W` is also
smooth and of finite rank, which the comparison with the cotangent symbol of `I_x` likewise
needs. On a boundaryless manifold, the commutator symbol of an operator of order at most `m + 1`
vanishes identically exactly when the operator has order at most `m`, and by polarization so does
its principal symbol. An operator of order zero is a `C^∞(M)`-linear map, and its principal
symbol is its fibre map.

## Main definitions

* `TauCeti.sectionCommutatorSymbol I hx`: the commutator symbol at an interior point `x`, a real
  multilinear map on the cotangent space `T_x*M` with values in `Hom(V_x, W_x)`, linear in the
  operator.
* `TauCeti.sectionPrincipalSymbol I hx P`: the principal symbol of `P` at `x`, a homogeneous
  function of degree `m` on `T_x*M` with values in `Hom(V_x, W_x)`.
* `TauCeti.sectionPrincipalSymbolₗ I hx P`: for `P` of order at most one, the principal symbol at
  `x` as a linear map on `T_x*M`.

## Main results

* `TauCeti.sectionCommutatorSymbol_mvfderiv`, `TauCeti.sectionPrincipalSymbol_mvfderiv`: the values
  at differentials of functions are the iterated commutators.
* `TauCeti.eq_sectionCommutatorSymbol_iff`: the commutator symbol is the multilinear map with
  these values.
* `TauCeti.sectionCommutatorSymbol_comp_perm`: the commutator symbol is symmetric.
  For an operator of order at most two this reads `[[P, ξ], η] = [[P, η], ξ]`
  (`TauCeti.sectionCommutatorSymbol_comm`).
* `TauCeti.smoothSectionFiberEquiv_cotangentSymbol`: comparison with the cotangent symbol of the
  vanishing ideal, through `I_x / I_x² ≃ T_x*M` and `Γ(V) / I_x Γ(V) ≃ V_x`.
* `TauCeti.sectionPrincipalSymbol_smul_covector`: the principal symbol is homogeneous of degree
  `m`; for `m = 1` it is moreover additive (`TauCeti.sectionPrincipalSymbol_add_covector`).
* `TauCeti.sectionCommutatorSymbol_eq_zero_of_mem_differentialOperators`,
  `TauCeti.sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators`: an operator of order at
  most `m`, viewed as one of order at most `m + 1`, has vanishing commutator and principal
  symbols.
* `TauCeti.forall_sectionCommutatorSymbol_eq_zero_iff`: on a boundaryless manifold, an operator of
  order at most `m + 1` has vanishing commutator symbol at every point exactly when it has order
  at most `m`.
* `TauCeti.forall_sectionPrincipalSymbol_eq_zero_iff`: on a boundaryless manifold, an operator of
  order at most `m + 1` has vanishing principal symbol at every point exactly when it has order at
  most `m`.
* `TauCeti.sectionPrincipalSymbol_mk_smul`: multiplying the values of an operator by a smooth
  function `g` multiplies its principal symbol at `x` by `g(x)`.
* `TauCeti.sectionPrincipalSymbol_mvfderiv_of_order_one`: a first-order operator has
  `σ_geom(P)(df_x) s(x) = P(f s)(x) - f(x) (P s)(x)`.
* `TauCeti.sectionCommutatorSymbol_mvfderiv_pair`: an operator of order at most two has
  `[[P, df_x], dg_x] s(x) = ([[P, f], g] s)(x)`.
* `TauCeti.sectionCommutatorSymbol_mvfderiv_of_order_two`: a second-order operator has
  `[[P, df_x], dg_x] s(x) = P(f g s)(x) - f(x) P(g s)(x) - g(x) P(f s)(x) + f(x) g(x) (P s)(x)`.
* `TauCeti.sectionPrincipalSymbol_eq_inv_two_smul_sectionCommutatorSymbol`: an operator of order
  at most two has `σ_geom(P)(ξ) = ½ [[P, ξ], ξ]`.
* `TauCeti.sectionPrincipalSymbol_comp`: principal symbols multiply under composition.
* `TauCeti.sectionPrincipalSymbol_restrictScalars`: the principal symbol of a `C^∞(M)`-linear map,
  as an operator of order zero, is its fibre map.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Bundle
open scoped ContDiff Manifold

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
  {x : M}

/-! ### The commutator symbol -/

variable (I) in
/-- The commutator symbol of a differential operator `P : Γ(V) → Γ(W)` of order at most `m` at
an interior point `x`: the real multilinear map on the cotangent space `T_x*M` sending
`(df₁(x), …, dfₘ(x))` to the linear map `V_x → W_x`, `s(x) ↦ ([⋯[P, f₁], …, fₘ] s)(x)`
(`TauCeti.sectionCommutatorSymbol_mvfderiv`). It is symmetric
(`TauCeti.sectionCommutatorSymbol_comp_perm`) and `m!` times the polarization of the principal
symbol `TauCeti.sectionPrincipalSymbol`. -/
def sectionCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ} :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m →ₗ[ℝ]
      MultilinearMap (RingHom.id ℝ) (fun _ : Fin m ↦ TangentSpace I x →L[ℝ] ℝ)
        (V x →ₗ[ℝ] W x) where
  toFun P := ((smoothSectionFiberMap x).compMultilinearMap
      (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m P)).compLinearMap
    fun _ ↦ covectorLift I hx
  map_add' P₁ P₂ := by ext; simp
  map_smul' c P := by ext; simp

/-- The commutator symbol at `(ξ₁, …, ξₘ)` is the fibre map at `x` of the iterated commutator with
the lifts of the covectors `ξᵢ`. -/
theorem sectionCommutatorSymbol_apply (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) :
    sectionCommutatorSymbol I hx P ξ =
      smoothSectionFiberMap x (commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m P
        fun i ↦ covectorLift I hx (ξ i)) :=
  (rfl)

/-! ### The principal symbol -/

variable (I) in
/-- The principal symbol of a differential operator `P : Γ(V) → Γ(W)` of order at most `m` at an
interior point `x`, in the geometric convention: the homogeneous function of degree `m` on the
cotangent space `T_x*M` with values in `Hom(V_x, W_x)` given by
`σ_geom(P)(df_x) s(x) = (1 / m!) ([⋯[P, f], …, f] s)(x)`, with `m` copies of `f`
(`TauCeti.sectionPrincipalSymbol_mvfderiv`). Its polarization is `1 / m!` times the commutator
symbol `TauCeti.sectionCommutatorSymbol`. -/
def sectionPrincipalSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : V x →ₗ[ℝ] W x :=
  (m.factorial : ℝ)⁻¹ • sectionCommutatorSymbol I hx P fun _ ↦ ξ

theorem sectionPrincipalSymbol_def (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P ξ =
      (m.factorial : ℝ)⁻¹ • sectionCommutatorSymbol I hx P fun _ ↦ ξ :=
  (rfl)

@[simp]
theorem sectionPrincipalSymbol_zero (hx : I.IsInteriorPoint x) {m : ℕ}
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
      (0 : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) ξ = 0 := by
  simp [sectionPrincipalSymbol_def]

@[simp]
theorem sectionPrincipalSymbol_add (hx : I.IsInteriorPoint x) {m : ℕ}
    (P₁ P₂ : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx (P₁ + P₂) ξ =
      sectionPrincipalSymbol I hx P₁ ξ + sectionPrincipalSymbol I hx P₂ ξ := by
  simp [sectionPrincipalSymbol_def, smul_add]

@[simp]
theorem sectionPrincipalSymbol_smul (hx : I.IsInteriorPoint x) {m : ℕ} (c : ℝ)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx (c • P) ξ = c • sectionPrincipalSymbol I hx P ξ := by
  simp only [sectionPrincipalSymbol_def, map_smul, smul_apply]
  exact smul_comm _ _ _

/-- The principal symbol of an operator of order at most `m` is homogeneous of degree `m`. -/
theorem sectionPrincipalSymbol_smul_covector (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) (c : ℝ)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P (c • ξ) = c ^ m • sectionPrincipalSymbol I hx P ξ := by
  have h := (sectionCommutatorSymbol I hx P).map_smul_univ (fun _ ↦ c) fun _ ↦ ξ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, RingHom.id_apply] at h
  rw [sectionPrincipalSymbol_def, sectionPrincipalSymbol_def, h]
  exact smul_comm _ _ _

/-- The principal symbol of an operator of order at most one is additive in the covector. -/
theorem sectionPrincipalSymbol_add_covector (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P (ξ + η) =
      sectionPrincipalSymbol I hx P ξ + sectionPrincipalSymbol I hx P η := by
  -- A family indexed by `Fin 1` is its value at `0`.
  have hu (ζ : TangentSpace I x →L[ℝ] ℝ) :
      Function.update (fun _ : Fin 1 ↦ ξ) 0 ζ = fun _ ↦ ζ :=
    funext fun j ↦ by rw [Fin.fin_one_eq_zero j, Function.update_self]
  have h := (sectionCommutatorSymbol I hx P).map_update_add (fun _ ↦ ξ) 0 ξ η
  rw [hu, hu, hu] at h
  rw [sectionPrincipalSymbol_def, sectionPrincipalSymbol_def, sectionPrincipalSymbol_def, h,
    smul_add]

variable (I) in
/-- The principal symbol at `x` of an operator of order at most one, as a linear map in the
covector. -/
def sectionPrincipalSymbolₗ (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] V x →ₗ[ℝ] W x where
  toFun := sectionPrincipalSymbol I hx P
  map_add' := sectionPrincipalSymbol_add_covector hx P
  map_smul' a ξ := by simpa using sectionPrincipalSymbol_smul_covector hx P a ξ

@[simp]
theorem sectionPrincipalSymbolₗ_apply (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbolₗ I hx P ξ = sectionPrincipalSymbol I hx P ξ :=
  (rfl)

@[simp]
theorem sectionPrincipalSymbol_neg (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx (-P) ξ = -sectionPrincipalSymbol I hx P ξ := by
  simp [sectionPrincipalSymbol_def]

@[simp]
theorem sectionPrincipalSymbol_sub (hx : I.IsInteriorPoint x) {m : ℕ}
    (P₁ P₂ : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx (P₁ - P₂) ξ =
      sectionPrincipalSymbol I hx P₁ ξ - sectionPrincipalSymbol I hx P₂ ξ := by
  simp [sectionPrincipalSymbol_def, smul_sub]

/-! ### Values at differentials of functions -/

/-- The commutator symbol at `x`, evaluated on the differentials at `x` of smooth functions
`f₁, …, fₘ` and on the value at `x` of a smooth section `s`, is the value at `x` of the iterated
commutator `[⋯[P, f₁], …, fₘ] s`. -/
theorem sectionCommutatorSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (f : Fin m → C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    sectionCommutatorSymbol I hx P (fun i ↦ mvfderiv I (f i) x) (s x) =
      commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m P f s x := by
  have h := apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (commutatorSymbol_covectorLift_sub_mem_smul_top hx P f s)
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  rwa [sectionCommutatorSymbol_apply, smoothSectionFiberMap_apply]

/-- The commutator symbol at `x` in two covectors, evaluated on the differentials at `x` of smooth
functions `f` and `g` and on the value at `x` of a smooth section `s`, is the value at `x` of the
double commutator `[[P, f], g] s`. -/
theorem sectionCommutatorSymbol_mvfderiv_pair (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (f g : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    sectionCommutatorSymbol I hx P ![mvfderiv I f x, mvfderiv I g x] (s x) =
      commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2 P ![f, g] s x := by
  rw [← sectionCommutatorSymbol_mvfderiv hx]
  congr 2
  funext i
  fin_cases i <;> rfl

/-- A real multilinear map on `T_x*M` with values in `Hom(V_x, W_x)` is the commutator symbol of
`P` at `x` as soon as it sends the differentials at `x` of smooth functions `f₁, …, fₘ` and the
value at `x` of a smooth section `s` to the value at `x` of `[⋯[P, f₁], …, fₘ] s`. -/
theorem eq_sectionCommutatorSymbol_iff (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (T : MultilinearMap (RingHom.id ℝ) (fun _ : Fin m ↦ TangentSpace I x →L[ℝ] ℝ)
      (V x →ₗ[ℝ] W x)) :
    T = sectionCommutatorSymbol I hx P ↔ ∀ (f : Fin m → C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯),
      T (fun i ↦ mvfderiv I (f i) x) (s x) =
        commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m P f s x := by
  refine ⟨fun h f s ↦ h ▸ sectionCommutatorSymbol_mvfderiv hx P f s, fun h ↦ ?_⟩
  ext ξ v
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (ξ i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) x) = ξ := funext hf
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply, h, sectionCommutatorSymbol_mvfderiv]

/-- The commutator symbol is symmetric. -/
theorem sectionCommutatorSymbol_comp_perm (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) (σ : Equiv.Perm (Fin m)) :
    sectionCommutatorSymbol I hx P (ξ ∘ σ) = sectionCommutatorSymbol I hx P ξ :=
  congr($((eq_sectionCommutatorSymbol_iff hx P
    ((sectionCommutatorSymbol I hx P).domDomCongr σ)).2 fun f s ↦ by
      rw [MultilinearMap.domDomCongr_apply, ← commutatorSymbol_comp_perm _ _ σ]
      exact sectionCommutatorSymbol_mvfderiv hx P (f ∘ σ) s) ξ)

/-- The commutator symbol of an operator of order at most two is symmetric in its two covectors. -/
theorem sectionCommutatorSymbol_comm (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (ξ η : TangentSpace I x →L[ℝ] ℝ) :
    sectionCommutatorSymbol I hx P ![ξ, η] = sectionCommutatorSymbol I hx P ![η, ξ] := by
  have h : ![η, ξ] ∘ Equiv.swap (0 : Fin 2) 1 = ![ξ, η] := by
    funext i
    fin_cases i <;> simp
  rw [← sectionCommutatorSymbol_comp_perm hx P ![η, ξ] (Equiv.swap 0 1), h]

/-- The commutator symbol of an operator of order at most `m + 1` vanishes at every interior point
if the operator has order at most `m`. -/
theorem sectionCommutatorSymbol_eq_zero_of_mem_differentialOperators (hx : I.IsInteriorPoint x)
    {m : ℕ} (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1))
    (hP : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    sectionCommutatorSymbol I hx P = 0 :=
  ((eq_sectionCommutatorSymbol_iff hx P 0).2 fun f s ↦ by
    simp [(commutatorSymbol_eq_zero_iff P).2 hP]).symm

/-- On a boundaryless manifold, an operator of order at most `m + 1` has vanishing commutator
symbol at every point if and only if it has order at most `m`. -/
theorem forall_sectionCommutatorSymbol_eq_zero_iff [BoundarylessManifold I M] {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)) :
    (∀ x : M, sectionCommutatorSymbol I (BoundarylessManifold.isInteriorPoint (x := x)) P = 0) ↔
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m := by
  rw [← commutatorSymbol_eq_zero_iff]
  constructor
  · intro h
    -- The iterated commutators are sections, so it suffices that their values vanish at every
    -- point.
    refine MultilinearMap.ext fun f ↦ LinearMap.ext fun s ↦ ContMDiffSection.ext fun y ↦ ?_
    rw [← sectionCommutatorSymbol_mvfderiv BoundarylessManifold.isInteriorPoint, h y]
    simp
  · exact fun h x ↦ sectionCommutatorSymbol_eq_zero_of_mem_differentialOperators _ P
      ((commutatorSymbol_eq_zero_iff P).1 h)

/-- Multiplying the values of `P` by a smooth function `g` multiplies its commutator symbol at
`x` by `g(x)`. -/
@[simp]
theorem sectionCommutatorSymbol_mk_smul (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (g : C^∞⟮I, M; ℝ⟯) :
    sectionCommutatorSymbol I hx
        ⟨g • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          smul_mem_differentialOperators g P.property⟩ =
      g x • sectionCommutatorSymbol I hx P :=
  ((eq_sectionCommutatorSymbol_iff hx _ _).2 fun f s ↦ by
    simp [sectionCommutatorSymbol_mvfderiv, commutatorSymbol_mk_smul]).symm

/-- The principal symbol at the differential of `f`, applied to the value at `x` of a section
`s`, is `1 / m!` times the value at `x` of the `m`-fold commutator `[⋯[P, f], …, f] s`. -/
theorem sectionPrincipalSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (f : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    sectionPrincipalSymbol I hx P (mvfderiv I f x) (s x) =
      (m.factorial : ℝ)⁻¹ •
        (smulCommutator ℝ f ^ m) (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s x := by
  rw [sectionPrincipalSymbol_def, LinearMap.smul_apply,
    sectionCommutatorSymbol_mvfderiv hx P (fun _ ↦ f) s, commutatorSymbol_const_apply]

/-- Multiplying the values of `P` by a smooth function `g` multiplies its principal symbol at `x`
by `g(x)`. -/
@[simp]
theorem sectionPrincipalSymbol_mk_smul (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (g : C^∞⟮I, M; ℝ⟯) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
        ⟨g • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          smul_mem_differentialOperators g P.property⟩ ξ =
      g x • sectionPrincipalSymbol I hx P ξ := by
  rw [sectionPrincipalSymbol_def, sectionPrincipalSymbol_def, sectionCommutatorSymbol_mk_smul,
    smul_apply]
  exact smul_comm _ _ _

/-- **The principal symbol of a first-order operator.** For an operator `P` of order at most one,
`σ_geom(P)(df_x) s(x) = P(f s)(x) - f(x) (P s)(x)`. -/
theorem sectionPrincipalSymbol_mvfderiv_of_order_one (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1)
    (f : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    sectionPrincipalSymbol I hx P (mvfderiv I f x) (s x) =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (f • s) x -
        f x • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s x := by
  rw [sectionPrincipalSymbol_mvfderiv]
  simp [smulCommutator_apply_apply, ContMDiffSection.smul_apply]

/-- **The commutator symbol of a second-order operator.** For an operator `P` of order at most two,
`[[P, df_x], dg_x] s(x) = P(f g s)(x) - f(x) P(g s)(x) - g(x) P(f s)(x) + f(x) g(x) (P s)(x)`. -/
theorem sectionCommutatorSymbol_mvfderiv_of_order_two (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (f g : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    sectionCommutatorSymbol I hx P ![mvfderiv I f x, mvfderiv I g x] (s x) =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (f • g • s) x -
        f x • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (g • s) x -
          g x • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (f • s) x +
            (f x * g x) • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s x := by
  rw [sectionCommutatorSymbol_mvfderiv_pair, commutatorSymbol_apply_apply]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    mul_apply_eq_comp, smulCommutator_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContMDiffSection.smul_apply, smul_comm g f s]
  module

/-- The principal symbol of an operator of order at most two is half its commutator symbol on the
diagonal: `σ_geom(P)(ξ) = ½ [[P, ξ], ξ]`. -/
theorem sectionPrincipalSymbol_eq_inv_two_smul_sectionCommutatorSymbol (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 2)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P ξ = (2 : ℝ)⁻¹ • sectionCommutatorSymbol I hx P ![ξ, ξ] := by
  rw [sectionPrincipalSymbol_def, Matrix.vec_single_eq_const, Matrix.vecCons_const,
    Nat.factorial_two, Nat.cast_ofNat]

/-- The principal symbol of an operator of order at most `m + 1` vanishes if the operator has
order at most `m`. -/
theorem sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators (hx : I.IsInteriorPoint x)
    {m : ℕ} (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1))
    (hP : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx P ξ = 0 := by
  simp [sectionPrincipalSymbol_def,
    sectionCommutatorSymbol_eq_zero_of_mem_differentialOperators hx P hP]

/-- On a boundaryless manifold, an operator of order at most `m + 1` has vanishing principal symbol
at every point if and only if it has order at most `m`. -/
theorem forall_sectionPrincipalSymbol_eq_zero_iff [BoundarylessManifold I M] {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)) :
    (∀ (x : M) (ξ : TangentSpace I x →L[ℝ] ℝ),
      sectionPrincipalSymbol I BoundarylessManifold.isInteriorPoint P ξ = 0) ↔
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m := by
  refine ⟨fun h ↦ (forall_sectionCommutatorSymbol_eq_zero_iff P).1 fun x ↦ ?_,
    fun hP x ↦ sectionPrincipalSymbol_eq_zero_of_mem_differentialOperators _ P hP⟩
  -- The commutator symbol is symmetric and vanishes on the diagonal, so it vanishes by
  -- polarization.
  have := HasUniqueDiv.of_isTorsionFree ℝ (V x →ₗ[ℝ] W x)
  refine MultilinearMap.eq_zero_of_apply_const_eq_zero
    (sectionCommutatorSymbol_comp_perm BoundarylessManifold.isInteriorPoint P) fun ξ ↦ ?_
  have hξ := h x ξ
  rw [sectionPrincipalSymbol_def, smul_eq_zero, inv_eq_zero] at hξ
  exact hξ.resolve_left (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

/-- **The principal symbol of an operator of order zero.** A `C^∞(M)`-linear map `L` of sections,
viewed as a differential operator of order zero, has principal symbol its fibre map at `x` at
every covector. -/
@[simp]
theorem sectionPrincipalSymbol_restrictScalars (hx : I.IsInteriorPoint x)
    (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
      ⟨L.restrictScalars ℝ, L.restrictScalars_mem_differentialOperators_zero⟩ ξ =
        smoothSectionFiberMap x L := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  refine ((smoothSectionFiberMap_eq_iff x L _).2 fun s ↦ ?_).symm
  rw [sectionPrincipalSymbol_mvfderiv]
  simp

section FiniteRank

variable [FiniteDimensional ℝ F'] [ContMDiffVectorBundle ∞ F' W I]
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  {U : M → Type*} [TopologicalSpace (TotalSpace F'' U)]
  [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)] [∀ x, TopologicalSpace (U x)]
  [FiberBundle F'' U] [VectorBundle ℝ F'' U]

/-- **Comparison with the cotangent symbol.** The commutator symbol at `x` is the cotangent symbol
`TauCeti.cotangentSymbol` of the vanishing ideal `I_x`, read through the identifications
`I_x / I_x² ≃ T_x*M` and `Γ(V) / I_x Γ(V) ≃ V_x`, `Γ(W) / I_x Γ(W) ≃ W_x`; the last needs `W`,
like `V`, to be smooth and of finite rank. -/
theorem smoothSectionFiberEquiv_cotangentSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (u : Fin m → (smoothVanishingIdeal I x).Cotangent) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionFiberEquiv I F' W x
        (cotangentSymbol ℝ (smoothVanishingIdeal I x) P u (Submodule.Quotient.mk s)) =
      sectionCommutatorSymbol I hx P (fun i ↦ smoothCotangentEquiv hx (u i)) (s x) := by
  choose a ha using fun i ↦ (smoothVanishingIdeal I x).toCotangent_surjective (u i)
  obtain rfl : (fun i ↦ (smoothVanishingIdeal I x).toCotangent (a i)) = u := funext ha
  simp only [smoothCotangentEquiv_toCotangent, cotangentSymbol_toCotangent,
    smoothSectionFiberEquiv_mk, sectionCommutatorSymbol_mvfderiv]

/-- **Principal symbols multiply under composition.** For operators `P : Γ(W) → Γ(U)` and
`Q : Γ(V) → Γ(W)` of orders at most `m` and `k`, where the intermediate bundle `W`, like `V`, is
smooth and of finite rank, the principal symbol of `P ∘ Q`, as an operator of order at most
`m + k`, is the composition of the principal symbols. -/
theorem sectionPrincipalSymbol_comp (hx : I.IsInteriorPoint x) {m k : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F'', U⟯ m)
    (Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ k)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx
        ⟨(P : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', U⟯) ∘ₗ (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯),
          comp_mem_differentialOperators P.property Q.property⟩ ξ =
      sectionPrincipalSymbol I hx P ξ ∘ₗ sectionPrincipalSymbol I hx Q ξ := by
  obtain ⟨f, rfl⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, mvfderiv I f x = ξ := ⟨_, mvfderiv_covectorLift hx ξ⟩
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  -- The value of the symbol of `Q` is the value at `x` of the section `t` below, and the
  -- `(m + k)`-fold commutator of `P ∘ Q` with `f` is `(m + k).choose m` times the composition of
  -- the commutators of `P` and `Q`; finally `(m + k).choose m / (m + k)! = 1 / (m! k!)`.
  set t : Cₛ^∞⟮I; F', W⟯ := (k.factorial : ℝ)⁻¹ •
    (smulCommutator ℝ f ^ k) (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s
  have hQ : sectionPrincipalSymbol I hx Q (mvfderiv I f x) (s x) = t x := by
    rw [sectionPrincipalSymbol_mvfderiv, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [ContMDiffSection.evalLinearMap_apply, LinearMap.comp_apply, hQ,
    sectionPrincipalSymbol_mvfderiv, sectionPrincipalSymbol_mvfderiv,
    smulCommutator_pow_comp_of_mem P.property Q.property]
  have hc : ((m + k).factorial : ℝ)⁻¹ * ((m + k).choose m : ℕ) =
      (m.factorial : ℝ)⁻¹ * (k.factorial : ℝ)⁻¹ := by
    rw [Nat.cast_add_choose]
    field_simp
  simp only [t, ← Nat.cast_smul_eq_nsmul ℝ, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    ContMDiffSection.coe_smul, Pi.smul_apply, smul_smul, hc]

end FiniteRank

end TauCeti
