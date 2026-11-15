/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.VanishingIdeal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.VanishingIdeal
public import TauCeti.RingTheory.Derivation.PrincipalSymbol
import Mathlib.Data.Nat.Choose.Cast
import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The principal symbol of a differential operator between sections of vector bundles

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff manifold `M`,
with `V` of finite rank, and let `P : Γ(V) → Γ(W)` be a differential operator of order at most `m`
in Grothendieck's sense of iterated commutators with multiplication by smooth functions
(`TauCeti.differentialOperators`); no continuity of `P` is assumed. With
`[P, f] = P ∘ M_f - M_f ∘ P`, the `m`-fold commutator `[⋯[P, f₁], …, fₘ]` is linear over the smooth
functions. Hence its value at `x` on a section `s` only depends on `s x`, and at an interior point
`x` it only depends on the differentials `(df₁)ₓ, …, (dfₘ)ₓ`, multilinearly and symmetrically.
This gives the **commutator symbol** of `P` at `x`,

`TauCeti.smoothSectionCommutatorSymbol I hx P : T_x*M × ⋯ × T_x*M → Hom(V_x, W_x)`,
`(df₁(x), …, dfₘ(x)) ↦ (s x ↦ ([⋯[P, f₁], …, fₘ] s)(x))`
(`TauCeti.smoothSectionCommutatorSymbol_mvfderiv`),

and the **principal symbol** of `P` at `x`, in the geometric convention without factors of `i`,

`TauCeti.smoothSectionPrincipalSymbol I hx P ξ = (1 / m!) σ(ξ, …, ξ) : V_x → W_x`,

so that `σ_geom(P)(df_x)(s x) = (1 / m!) ([⋯[P, f], …, f] s)(x)` with `m` copies of `f`
(`TauCeti.smoothSectionPrincipalSymbol_mvfderiv`). In the Fourier convention of pseudodifferential
operators, where `∂ⱼ` has symbol `i ξⱼ`, the principal symbol of an operator of order `m` is `i ^ m`
times this one. These are the bundle-valued analogues of the symbols
`TauCeti.smoothCommutatorSymbol` and `TauCeti.smoothPrincipalSymbol` of operators on smooth
functions.

The commutator symbol at `x` is the algebraic cotangent symbol `TauCeti.cotangentSymbol` of the
vanishing ideal `I_x`, read through the identifications `I_x / I_x² ≃ T_x*M`
(`TauCeti.smoothCotangentEquiv`) and `Γ(V) / I_x Γ(V) ≃ V_x` (`TauCeti.smoothSectionFiberEquiv`)
(`TauCeti.smoothSectionFiberEquiv_cotangentSymbol`).

## Main definitions

* `TauCeti.smoothSectionCommutatorSymbol I hx`: the commutator symbol at an interior point `x`, a
  real multilinear map from the cotangent space `T_x*M` to `V_x →ₗ[ℝ] W_x`, linear in the operator.
* `TauCeti.smoothSectionPrincipalSymbol I hx P`: the principal symbol of `P` at `x`, a homogeneous
  map of degree `m` from `T_x*M` to `V_x →ₗ[ℝ] W_x`.

## Main results

* `LinearMap.apply_apply_eq_of_apply_eq`: a map of sections that is linear over the smooth
  functions is tensorial, its value at `x` only depends on the value of the section at `x`.
* `TauCeti.smoothSectionCommutatorSymbol_mvfderiv`, `TauCeti.smoothSectionPrincipalSymbol_mvfderiv`:
  the values at differentials of functions are the iterated commutators.
* `TauCeti.smoothSectionCommutatorSymbol_comp_perm`: the commutator symbol is symmetric.
* `TauCeti.smoothSectionFiberEquiv_cotangentSymbol`: comparison with the cotangent symbol.
* `TauCeti.forall_smoothSectionCommutatorSymbol_eq_zero_iff`: on a boundaryless manifold, an
  operator of order at most `m + 1` has vanishing commutator symbol at every point exactly when it
  has order at most `m`.
* `TauCeti.smoothSectionPrincipalSymbol_smul_covector`: the principal symbol is homogeneous of
  degree `m`.
* `TauCeti.smoothSectionPrincipalSymbol_comp`: principal symbols multiply under composition,
  `σ(P ∘ Q)(ξ) = σ(P)(ξ) ∘ σ(Q)(ξ)`.
* `TauCeti.smoothSectionPrincipalSymbol_smul_function`: multiplying an operator by a smooth
  function `g` multiplies its principal symbol at `x` by `g x`.
* `TauCeti.smoothSectionPrincipalSymbol_order_zero_apply`: an operator of order zero, that is a
  map of sections linear over the smooth functions, has as principal symbol its fibre map at `x`.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§12, 19.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]
  {x : M}

/-! ### Linear maps over smooth functions are tensorial -/

namespace LinearMap

variable [FiniteDimensional ℝ F]

/-- A map of sections that is linear over the smooth functions sends a section vanishing at `x`
to a section vanishing at `x`. -/
theorem apply_apply_eq_zero_of_apply_eq_zero
    (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) {s : Cₛ^∞⟮I; F, V⟯} (hs : s x = 0) :
    L s x = 0 := by
  refine TauCeti.apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top ?_
  have h := Submodule.mem_map_of_mem (f := L)
    (TauCeti.mem_smoothVanishingIdeal_smul_top_of_apply_eq_zero hs)
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

/-- **Tensoriality.** The value at `x` of the image of a section under a map of sections that is
linear over the smooth functions only depends on the value of the section at `x`. -/
theorem apply_apply_eq_of_apply_eq
    (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) {s t : Cₛ^∞⟮I; F, V⟯} (h : s x = t x) :
    L s x = L t x := by
  have hst := L.apply_apply_eq_zero_of_apply_eq_zero (x := x) (s := s - t) (by simp [h])
  rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at hst

end LinearMap

namespace TauCeti

/-! ### Lifting covectors and fibre vectors -/

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
variable (I) in
private theorem exists_toCotangent_comp_eq_id (x : M) :
    ∃ g : (smoothVanishingIdeal I x).Cotangent →ₗ[ℝ] smoothVanishingIdeal I x,
      (smoothVanishingIdeal I x).toCotangent.restrictScalars ℝ ∘ₗ g = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ <|
    LinearMap.range_eq_top.2 (smoothVanishingIdeal I x).toCotangent_surjective

/-- A real-linear choice of a smooth function vanishing at `x` with prescribed differential at
`x`. -/
private def covectorLift (hx : I.IsInteriorPoint x) :
    (TangentSpace I x →L[ℝ] ℝ) →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ :=
  (smoothVanishingIdeal I x).subtype.restrictScalars ℝ ∘ₗ
    (exists_toCotangent_comp_eq_id I x).choose ∘ₗ (smoothCotangentEquiv hx).symm.toLinearMap

private theorem covectorLift_apply_self (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : covectorLift hx ξ x = 0 :=
  mem_smoothVanishingIdeal_iff.mp (Subtype.prop _)

private theorem mvfderiv_covectorLift (hx : I.IsInteriorPoint x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : mvfderiv I (covectorLift hx ξ) x = ξ := by
  set r := exists_toCotangent_comp_eq_id I x
  have h := LinearMap.congr_fun r.choose_spec ((smoothCotangentEquiv hx).symm ξ)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.id_apply] at h
  have hξ : covectorLift hx ξ = (r.choose ((smoothCotangentEquiv hx).symm ξ) : C^∞⟮I, M; ℝ⟯) :=
    (rfl)
  rw [hξ, ← smoothCotangentEquiv_toCotangent hx, h, LinearEquiv.apply_symm_apply]

variable (I F V) in
private theorem exists_evalLinearMap_comp_eq_id (x : M) :
    ∃ g : V x →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯, ContMDiffSection.evalLinearMap I F ∞ V x ∘ₗ g = LinearMap.id :=
  LinearMap.exists_rightInverse_of_surjective _ <|
    LinearMap.range_eq_top.2 (ContMDiffSection.evalLinearMap_surjective ∞ x)

variable (I F V) in
/-- A real-linear choice of a smooth section through each vector of the fibre at `x`. -/
private def sectionLift (x : M) : V x →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯ :=
  (exists_evalLinearMap_comp_eq_id I F V x).choose

private theorem sectionLift_apply_self (v : V x) : sectionLift I F V x v x = v := by
  have h := LinearMap.congr_fun (exists_evalLinearMap_comp_eq_id I F V x).choose_spec v
  rw [LinearMap.comp_apply, ContMDiffSection.evalLinearMap_apply, LinearMap.id_apply] at h
  exact h

/-- Every vector of the fibre at `x` is the value of a smooth section. -/
private theorem exists_apply_eq (v : V x) : ∃ s : Cₛ^∞⟮I; F, V⟯, s x = v :=
  ⟨sectionLift I F V x v, sectionLift_apply_self v⟩

variable (I F V F' W) in
/-- The fibre map at `x` of a map of sections that is linear over the smooth functions. -/
private def fiberMap (x : M) :
    (Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯) →ₗ[ℝ] (V x →ₗ[ℝ] W x) where
  toFun L := ContMDiffSection.evalLinearMap I F' ∞ W x ∘ₗ L.restrictScalars ℝ ∘ₗ sectionLift I F V x
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-! ### The commutator symbol and the principal symbol -/

variable (I) in
/-- The commutator symbol of a differential operator `P : Γ(V) → Γ(W)` of order at most `m` at an
interior point `x`: the real multilinear map on the cotangent space `T_x*M` sending
`(df₁(x), …, dfₘ(x))` to the map `s x ↦ ([⋯[P, f₁], …, fₘ] s)(x)` from `V_x` to `W_x`
(`TauCeti.smoothSectionCommutatorSymbol_mvfderiv`). It is symmetric
(`TauCeti.smoothSectionCommutatorSymbol_comp_perm`) and `m!` times the polarization of the
principal symbol `TauCeti.smoothSectionPrincipalSymbol`. -/
def smoothSectionCommutatorSymbol (hx : I.IsInteriorPoint x) {m : ℕ} :
    differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m →ₗ[ℝ]
      MultilinearMap (RingHom.id ℝ) (fun _ : Fin m ↦ TangentSpace I x →L[ℝ] ℝ) (V x →ₗ[ℝ] W x)
      where
  toFun P := ((fiberMap I F V F' W x).compMultilinearMap
      ((commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) P)).compLinearMap
    fun _ ↦ covectorLift hx
  map_add' P₁ P₂ := by ext; simp
  map_smul' c P := by ext; simp

variable (I) in
/-- The principal symbol of a differential operator `P : Γ(V) → Γ(W)` of order at most `m` at an
interior point `x`, in the geometric convention: the homogeneous map of degree `m` from the
cotangent space `T_x*M` to `V_x →ₗ[ℝ] W_x` given by
`σ_geom(P)(df_x)(s x) = (1 / m!) ([⋯[P, f], …, f] s)(x)`, with `m` copies of `f`
(`TauCeti.smoothSectionPrincipalSymbol_mvfderiv`). Its polarization is `1 / m!` times the
commutator symbol `TauCeti.smoothSectionCommutatorSymbol`. -/
def smoothSectionPrincipalSymbol (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : V x →ₗ[ℝ] W x :=
  (m.factorial : ℝ)⁻¹ • smoothSectionCommutatorSymbol I hx P fun _ ↦ ξ

theorem smoothSectionPrincipalSymbol_def (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx P ξ =
      (m.factorial : ℝ)⁻¹ • smoothSectionCommutatorSymbol I hx P fun _ ↦ ξ :=
  (rfl)

@[simp]
theorem smoothSectionPrincipalSymbol_zero (hx : I.IsInteriorPoint x) {m : ℕ}
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx
      (0 : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) ξ = 0 := by
  simp [smoothSectionPrincipalSymbol_def]

@[simp]
theorem smoothSectionPrincipalSymbol_add (hx : I.IsInteriorPoint x) {m : ℕ}
    (P₁ P₂ : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx (P₁ + P₂) ξ =
      smoothSectionPrincipalSymbol I hx P₁ ξ + smoothSectionPrincipalSymbol I hx P₂ ξ := by
  simp [smoothSectionPrincipalSymbol_def]

@[simp]
theorem smoothSectionPrincipalSymbol_smul (hx : I.IsInteriorPoint x) {m : ℕ} (c : ℝ)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx (c • P) ξ = c • smoothSectionPrincipalSymbol I hx P ξ := by
  simp only [smoothSectionPrincipalSymbol_def, map_smul, smul_apply]
  rw [smul_comm]

/-- The principal symbol of an operator of order at most `m` is homogeneous of degree `m`. -/
theorem smoothSectionPrincipalSymbol_smul_covector (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) (c : ℝ)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx P (c • ξ) =
      c ^ m • smoothSectionPrincipalSymbol I hx P ξ := by
  have h := (smoothSectionCommutatorSymbol I hx P).map_smul_univ (fun _ ↦ c) fun _ ↦ ξ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, RingHom.id_apply] at h
  rw [smoothSectionPrincipalSymbol_def, smoothSectionPrincipalSymbol_def, h, smul_comm]

/-! ### Values on differentials and fibre vectors -/

variable [FiniteDimensional ℝ F]

private theorem fiberMap_apply_apply (L : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F', W⟯)
    (s : Cₛ^∞⟮I; F, V⟯) : fiberMap I F V F' W x L (s x) = L s x := by
  simp only [fiberMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, ContMDiffSection.evalLinearMap_apply]
  exact L.apply_apply_eq_of_apply_eq (sectionLift_apply_self _)

/-- The commutator symbol at `x`, evaluated on the differentials at `x` of smooth functions
`f₁, …, fₘ` and on the value at `x` of a section `s`, is the value at `x` of the iterated
commutator `[⋯[P, f₁], …, fₘ] s`. -/
theorem smoothSectionCommutatorSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (f : Fin m → C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionCommutatorSymbol I hx P (fun i ↦ mvfderiv I (f i) x) (s x) =
      commutatorSymbol ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m P f s x := by
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
  have h := apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (commutatorSymbol_apply_sub_mem_smul_top P hg s)
  rw [commutatorSymbol_add_algebraMap, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  rw [← h]
  exact fiberMap_apply_apply _ s

/-- The commutator symbol is symmetric. -/
theorem smoothSectionCommutatorSymbol_comp_perm (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) (σ : Equiv.Perm (Fin m)) :
    smoothSectionCommutatorSymbol I hx P (ξ ∘ σ) = smoothSectionCommutatorSymbol I hx P ξ := by
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (ξ i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) x) = ξ := funext hf
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨s, rfl⟩ := exists_apply_eq (I := I) (F := F) v
  have h := smoothSectionCommutatorSymbol_mvfderiv hx P (f ∘ σ) s
  rw [commutatorSymbol_comp_perm, ← smoothSectionCommutatorSymbol_mvfderiv hx P f s] at h
  exact h

/-- **Comparison with the cotangent symbol.** The commutator symbol at `x` is the cotangent symbol
`TauCeti.cotangentSymbol` of the vanishing ideal `I_x`, read through the identifications
`I_x / I_x² ≃ T_x*M` and `Γ(V) / I_x Γ(V) ≃ V_x`, `Γ(W) / I_x Γ(W) ≃ W_x`. -/
theorem smoothSectionFiberEquiv_cotangentSymbol [FiniteDimensional ℝ F']
    [ContMDiffVectorBundle ∞ F' W I] (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (u : Fin m → (smoothVanishingIdeal I x).Cotangent) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionFiberEquiv I F' W x
        (cotangentSymbol ℝ (smoothVanishingIdeal I x) P u (Submodule.Quotient.mk s)) =
      smoothSectionCommutatorSymbol I hx P (fun i ↦ smoothCotangentEquiv hx (u i)) (s x) := by
  choose a ha using fun i ↦ (smoothVanishingIdeal I x).toCotangent_surjective (u i)
  obtain rfl : (fun i ↦ (smoothVanishingIdeal I x).toCotangent (a i)) = u := funext ha
  simp only [smoothCotangentEquiv_toCotangent, cotangentSymbol_toCotangent,
    smoothSectionFiberEquiv_mk]
  rw [smoothSectionCommutatorSymbol_mvfderiv]

/-- The commutator symbol of an operator of order at most `m + 1` vanishes at every interior point
if the operator has order at most `m`. -/
theorem smoothSectionCommutatorSymbol_eq_zero_of_mem_differentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1))
    (hP : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m) :
    smoothSectionCommutatorSymbol I hx P = 0 := by
  ext ξ v
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (ξ i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) x) = ξ := funext hf
  obtain ⟨s, rfl⟩ := exists_apply_eq (I := I) (F := F) v
  simp [smoothSectionCommutatorSymbol_mvfderiv, (commutatorSymbol_eq_zero_iff P).2 hP]

/-- On a boundaryless manifold, an operator of order at most `m + 1` has vanishing commutator
symbol at every point if and only if it has order at most `m`. -/
theorem forall_smoothSectionCommutatorSymbol_eq_zero_iff [BoundarylessManifold I M] {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1)) :
    (∀ x : M,
        smoothSectionCommutatorSymbol I (BoundarylessManifold.isInteriorPoint (x := x)) P = 0) ↔
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
        differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m := by
  rw [← commutatorSymbol_eq_zero_iff]
  constructor
  · intro h
    refine MultilinearMap.ext fun f ↦ LinearMap.ext fun s ↦ ContMDiffSection.ext fun y ↦ ?_
    rw [← smoothSectionCommutatorSymbol_mvfderiv BoundarylessManifold.isInteriorPoint, h y]
    simp
  · exact fun h x ↦ smoothSectionCommutatorSymbol_eq_zero_of_mem_differentialOperators _ P
      ((commutatorSymbol_eq_zero_iff P).1 h)

/-! ### Properties of the principal symbol -/

/-- The principal symbol at the differential of `f`, on the value of a section `s`, is `1 / m!`
times the value at `x` of the `m`-fold commutator `[⋯[P, f], …, f] s`. -/
theorem smoothSectionPrincipalSymbol_mvfderiv (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (f : C^∞⟮I, M; ℝ⟯) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionPrincipalSymbol I hx P (mvfderiv I f x) (s x) =
      (m.factorial : ℝ)⁻¹ •
        (smulCommutator ℝ f ^ m) (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s x := by
  rw [smoothSectionPrincipalSymbol_def, LinearMap.smul_apply,
    smoothSectionCommutatorSymbol_mvfderiv hx P fun _ ↦ f, commutatorSymbol_const_apply]

/-- The principal symbol of an operator of order at most `m + 1` vanishes if the operator has
order at most `m`. -/
theorem smoothSectionPrincipalSymbol_eq_zero_of_mem_differentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (m + 1))
    (hP : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∈
      differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx P ξ = 0 := by
  simp [smoothSectionPrincipalSymbol_def,
    smoothSectionCommutatorSymbol_eq_zero_of_mem_differentialOperators hx P hP]

/-- Multiplying the values of `P` by a smooth function `g` multiplies its principal symbol at `x`
by `g x`. -/
theorem smoothSectionPrincipalSymbol_smul_function (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (g : C^∞⟮I, M; ℝ⟯) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx
        ⟨g • (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯), smul_mem_differentialOperators g P.2⟩ ξ =
      g x • smoothSectionPrincipalSymbol I hx P ξ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨s, rfl⟩ := exists_apply_eq (I := I) (F := F) v
  rw [LinearMap.smul_apply, smoothSectionPrincipalSymbol_mvfderiv,
    smoothSectionPrincipalSymbol_mvfderiv, ← commutatorSymbol_const_apply,
    ← commutatorSymbol_const_apply, commutatorSymbol_mk_smul]
  simp only [smul_apply, LinearMap.smul_apply, ContMDiffSection.smul_apply]
  rw [smul_comm]

/-- An operator of order at most zero, that is a map of sections linear over the smooth functions,
has as principal symbol at every covector its fibre map at `x`: `σ(P)(ξ)(s x) = (P s)(x)`. -/
theorem smoothSectionPrincipalSymbol_order_zero_apply (hx : I.IsInteriorPoint x)
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 0)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (s : Cₛ^∞⟮I; F, V⟯) :
    smoothSectionPrincipalSymbol I hx P ξ (s x) = (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s x := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  simp [smoothSectionPrincipalSymbol_mvfderiv]

section Comp

variable {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace ℝ F''] [FiniteDimensional ℝ F'']
  {V'' : M → Type*} [TopologicalSpace (TotalSpace F'' V'')]
  [∀ x, AddCommGroup (V'' x)] [∀ x, Module ℝ (V'' x)] [∀ x, TopologicalSpace (V'' x)]
  [FiberBundle F'' V''] [VectorBundle ℝ F'' V''] [ContMDiffVectorBundle ∞ F'' V'' I]

/-- **Principal symbols multiply under composition.** For operators `Q : Γ(V) → Γ(V'')` and
`P : Γ(V'') → Γ(W)` of orders at most `k` and `m`, the principal symbol of `P ∘ Q`, as an
operator of order at most `m + k`, is the composition of the principal symbols:
`σ(P ∘ Q)(ξ) = σ(P)(ξ) ∘ σ(Q)(ξ)`. -/
theorem smoothSectionPrincipalSymbol_comp (hx : I.IsInteriorPoint x) {m k : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F'', V''⟯ Cₛ^∞⟮I; F', W⟯ m)
    (Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F'', V''⟯ k)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    smoothSectionPrincipalSymbol I hx
        ⟨(P : Cₛ^∞⟮I; F'', V''⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) ∘ₗ
            (Q : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F'', V''⟯),
          comp_mem_differentialOperators P.2 Q.2⟩ ξ =
      smoothSectionPrincipalSymbol I hx P ξ ∘ₗ smoothSectionPrincipalSymbol I hx Q ξ := by
  obtain ⟨f, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) ξ
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨s, rfl⟩ := exists_apply_eq (I := I) (F := F) v
  -- The `(m + k)`-fold commutator of `P ∘ Q` with `f` is `(m + k).choose m` times the composition
  -- of the commutators of `P` and `Q`, and `(m + k).choose m / (m + k)! = 1 / (m! k!)`.
  have key := congr($(commutatorSymbol_comp_const P Q f) s x)
  rw [LinearMap.smul_apply, LinearMap.comp_apply, ← Nat.cast_smul_eq_nsmul ℝ,
    ContMDiffSection.coe_smul, Pi.smul_apply] at key
  rw [LinearMap.comp_apply, smoothSectionPrincipalSymbol_def, LinearMap.smul_apply,
    smoothSectionCommutatorSymbol_mvfderiv hx _ fun _ ↦ f, key,
    smoothSectionPrincipalSymbol_def, smoothSectionPrincipalSymbol_def, LinearMap.smul_apply,
    LinearMap.smul_apply, smoothSectionCommutatorSymbol_mvfderiv hx Q fun _ ↦ f, map_smul,
    smoothSectionCommutatorSymbol_mvfderiv hx P fun _ ↦ f, smul_smul, smul_smul,
    Nat.cast_add_choose]
  congr 1
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 m.factorial_ne_zero
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hmk : ((m + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (m + k).factorial_ne_zero
  field_simp

end Comp

end TauCeti
