/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Jet
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Symbol
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.RingTheory.Ideal.Operations

/-!
# Top-order jets and the principal symbol

Let `V` be a smooth real vector bundle of finite rank over a finite-dimensional Hausdorff
boundaryless manifold `M`, and `JᵣV` its bundle of `r`-jets. A differential operator
`P : Γ(V) → Γ(W)` of order at most `r`, in Grothendieck's sense of iterated commutators with
multiplication operators, factors at every point through jets: `(P s)(x) = A_x (jʳs(x))` for a
unique linear map `A_x : (JᵣV)_x → W_x`, its jet factor
(`LinearMap.jetFactorOfMemDifferentialOperators`). Its principal symbol is defined through
`r`-fold commutators (`TauCeti.sectionCommutatorSymbol`). This file compares the two descriptions,
through the jets of top order.

The `r`-jet prolongation `jʳ : Γ(V) → Γ(JᵣV)` (`TauCeti.JetBundle.jetProlongation`) is itself a
differential operator of order at most `r`. Its commutator symbol at `x`
(`TauCeti.JetBundle.jetSymbol`) is the symmetric multilinear map

`(T_x*M)ʳ → Hom(V_x, (JᵣV)_x)`, `(df₁(x), …, dfᵣ(x)) ↦ (s(x) ↦ jʳ(f₁ ⋯ fᵣ • s)(x))`

for smooth functions `fᵢ` vanishing at `x` (`TauCeti.JetBundle.jetSymbol_mvfderiv`). Its values
span the jets of top order: for `r = k + 1`, the kernel of the truncation
`(J_{k+1}V)_x → (J_kV)_x` (`TauCeti.JetBundle.ker_truncate_eq_span_jetSymbol`), which is onto
(`TauCeti.JetBundle.truncate_surjective`). So through symmetric tensors the symbol induces a
linear map from `Sym^(k+1) T_x*M ⊗ V_x` onto this kernel. Indeed a jet with vanishing truncation is
the jet of a section in `I_x ^ (k + 1) Γ(V)`, a finite sum of products `f₁ ⋯ f_{k+1} • s` of
functions vanishing at `x` with a section (`Ideal.pow_smul_eq_span_prod_smul`).

On these jets the jet factor of an operator `P` of order at most `r` is its commutator symbol:

`A_x (jetSymbol(ξ₁, …, ξᵣ) v) = σ(P)(ξ₁, …, ξᵣ) v`

(`LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol`), so the principal symbol is
`σ(P)(ξ) v = (1 / r!) A_x (jetSymbol(ξ, …, ξ) v)`
(`LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol_const`). Both sides are
`(P (f₁ ⋯ fᵣ • s))(x)`: in the expanded iterated commutator every other term carries a factor
`fᵢ(x) = 0`. Consequently an operator of order at most `k + 1` has vanishing commutator symbol at
`x` exactly when its jet factor kills the jets of top order there
(`TauCeti.sectionCommutatorSymbol_eq_zero_iff_ker_truncate_le`), and it has order at
most `k` exactly when its jet factors all factor through the truncation to `k`-jets
(`TauCeti.mem_differentialOperators_iff_forall_ker_truncate_le`); for `r' ≤ r`, the jet factor of
order `r` of an operator of order at most `r'` is its jet factor of order `r'` composed with the
truncation (`LinearMap.jetFactorOfMemDifferentialOperators_eq_comp_truncate`).

The jets of top order are also the image of the inclusion `TauCeti.JetBundle.ofTop` of continuous
multilinear maps `TₓM × ⋯ × TₓM → Vₓ`. Through it the principal symbol is the restriction of the
jet factor `A_x` to the top-order jets,

`σ(P)(ξ) v = A_x (ofTop (ξ ⊗ ⋯ ⊗ ξ ⊗ v))`,

where `ξ ⊗ ⋯ ⊗ ξ ⊗ v` is the multilinear map `(v₁, …, vᵣ) ↦ ξ(v₁) ⋯ ξ(vᵣ) v`
(`TauCeti.sectionPrincipalSymbol_apply_eq_jetFactorOfMemDifferentialOperators`), and the
commutator symbol is `[⋯[P, ξ₁], …, ξᵣ] v = A_x (ofTop (r! • (ξ₁ ⊗ ⋯ ⊗ ξᵣ ⊗ v)))`
(`TauCeti.sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators`), since the jet of
`f₁ ⋯ fᵣ s` at `x` is `ofTop (r! • (dₓf₁ ⊗ ⋯ ⊗ dₓfᵣ ⊗ s(x)))` (`TauCeti.JetBundle.jet_prod_smul`).

## Main definitions

* `TauCeti.JetBundle.jetSymbol`: the commutator symbol at a point of the `r`-jet prolongation
  `TauCeti.JetBundle.jetProlongation`.

## Main results

* `TauCeti.JetBundle.jetSymbol_mvfderiv`: the symbol on differentials of functions vanishing at
  `x` is the jet of their product with a section.
* `TauCeti.JetBundle.ker_truncate_eq_span_jetSymbol`: the jets of order `k + 1` with vanishing
  truncation to order `k` are spanned by the values of the symbol.
* `LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol`: the jet factor of an operator
  on the values of the symbol is the commutator symbol of the operator.
* `TauCeti.mem_differentialOperators_iff_forall_ker_truncate_le`: the order filtration
  of differential operators through truncation of jets.
* `TauCeti.sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators`,
  `TauCeti.sectionPrincipalSymbol_apply_eq_jetFactorOfMemDifferentialOperators`: the commutator
  and principal symbols are the jet factor on the top-order jets `TauCeti.JetBundle.ofTop`.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12, 19 (jets and the symbol of a linear differential operator).
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] {r : ℕ}

namespace JetBundle

/-! ### The symbol of the jet prolongation -/

variable (I F V r) in
/-- The **symbol of the `r`-jet prolongation** at `x`: the commutator symbol of
`jʳ : Γ(V) → Γ(JᵣV)` (`TauCeti.sectionCommutatorSymbol`), a symmetric real-multilinear map on the
cotangent space `T_x*M` with values in `Hom(V_x, (JᵣV)_x)`. It sends `(df₁(x), …, dfᵣ(x))` and
`s(x)` to the `r`-jet `jʳ(f₁ ⋯ fᵣ • s)(x)` whenever the functions `fᵢ` vanish at `x`
(`TauCeti.JetBundle.jetSymbol_mvfderiv`). Its values span the jets of top order, the kernel of the
truncation to lower order (`TauCeti.JetBundle.ker_truncate_eq_span_jetSymbol`), so through
symmetric tensors it induces a linear map from `Sym^r T_x*M ⊗ V_x` onto these jets. -/
def jetSymbol (x : M) :
    MultilinearMap (RingHom.id ℝ) (fun _ : Fin r ↦ TangentSpace I x →L[ℝ] ℝ)
      (V x →ₗ[ℝ] JetBundle I F V r x) :=
  sectionCommutatorSymbol I BoundarylessManifold.isInteriorPoint
    ⟨jetProlongation I F V r, jetProlongation_mem_differentialOperators⟩

theorem jetSymbol_def (x : M) :
    jetSymbol I F V r x =
      sectionCommutatorSymbol I BoundarylessManifold.isInteriorPoint
        ⟨jetProlongation I F V r, jetProlongation_mem_differentialOperators⟩ :=
  (rfl)

/-- **The symbol of the jet prolongation on differentials.** For smooth functions `f₁, …, fᵣ`
vanishing at `x` and a smooth section `s`, the symbol at `(df₁(x), …, dfᵣ(x))` sends `s(x)` to the
`r`-jet at `x` of `f₁ ⋯ fᵣ • s`. -/
theorem jetSymbol_mvfderiv {x : M} {f : Fin r → C^∞⟮I, M; ℝ⟯} (hf : ∀ i, f i x = 0)
    (s : Cₛ^∞⟮I; F, V⟯) :
    jetSymbol I F V r x (fun i ↦ mvfderiv I (f i) x) (s x) =
      jet I F r ((∏ i, f i) • s : Cₛ^∞⟮I; F, V⟯) x := by
  rw [jetSymbol_def, sectionCommutatorSymbol_mvfderiv_of_forall_apply_eq_zero _ _ hf s]
  exact jetProlongation_apply _ x

/-- The symbol of the jet prolongation is symmetric. -/
theorem jetSymbol_comp_perm (x : M) (ξ : Fin r → TangentSpace I x →L[ℝ] ℝ)
    (σ : Equiv.Perm (Fin r)) :
    jetSymbol I F V r x (ξ ∘ σ) = jetSymbol I F V r x ξ := by
  rw [jetSymbol_def]
  exact sectionCommutatorSymbol_comp_perm _ _ ξ σ

/-! ### Jets of top order -/

/-- **The symbol takes values in the jets of top order.** The values of the symbol of the
`(k + 1)`-jet prolongation have vanishing truncation to `k`-jets. -/
@[simp]
theorem truncate_jetSymbol {k : ℕ} (x : M) (ξ : Fin (k + 1) → TangentSpace I x →L[ℝ] ℝ)
    (v : V x) :
    truncate (I := I) (F := F) (V := V) (Nat.le_add_right k 1) x
      (jetSymbol I F V (k + 1) x ξ v) = 0 := by
  obtain ⟨f, s, hf, rfl, rfl⟩ := exists_mvfderiv_eq_and_apply_eq (F := F) x ξ v
  rw [jetSymbol_mvfderiv hf, truncate_jet]
  exact jet_eq_zero_of_mem_smoothVanishingIdeal_pow_smul_top
    ((Ideal.pow_smul_eq_span_prod_smul _ _ _).ge (Submodule.subset_span
      ⟨f, fun i ↦ mem_smoothVanishingIdeal_iff.2 (hf i), s, Submodule.mem_top, rfl⟩))

/-- **The jets of top order.** The `(k + 1)`-jets at `x` with vanishing truncation to `k`-jets are
the linear combinations of the values of the symbol of the jet prolongation: a jet with vanishing
truncation is the jet of a section in `I_x ^ (k + 1) Γ(V)`, a finite sum of sections
`f₁ ⋯ f_{k+1} • s` with all `fᵢ` vanishing at `x`. Together with
`TauCeti.JetBundle.truncate_surjective`, this describes the truncation sequence of jets
`(J_{k+1}V)_x → (J_kV)_x → 0`: its kernel is spanned by the image of `Sym^(k+1) T_x*M ⊗ V_x`. -/
theorem ker_truncate_eq_span_jetSymbol {k : ℕ} (x : M) :
    LinearMap.ker
        (truncate (I := I) (F := F) (V := V) (Nat.le_add_right k 1) x).toLinearMap =
      Submodule.span ℝ {B | ∃ ξ v, jetSymbol I F V (k + 1) x ξ v = B} := by
  refine le_antisymm (fun B hB ↦ ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨s, rfl⟩ := jetLinearMap_surjective x B
    rw [LinearMap.mem_ker, jetLinearMap_apply, ContinuousLinearMap.coe_coe, truncate_jet,
      jet_eq_zero_iff_mem_smoothVanishingIdeal_pow_smul_top,
      Ideal.pow_smul_eq_span_prod_smul] at hB
    -- The `(k + 1)`-jet at `x` is not linear over the smooth functions, so the induction carries
    -- all multiples `g • t` of the spanned sections `t`.
    suffices ∀ g : C^∞⟮I, M; ℝ⟯, jet I F (k + 1) (g • s : Cₛ^∞⟮I; F, V⟯) x ∈
        Submodule.span ℝ {B | ∃ ξ v, jetSymbol I F V (k + 1) x ξ v = B} by
      simpa using this 1
    induction hB using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨f, hf, z, -, rfl⟩ := ht
      intro g
      refine Submodule.subset_span ⟨fun i ↦ mvfderiv I (f i) x, (g • z) x, ?_⟩
      rw [jetSymbol_mvfderiv (fun i ↦ mem_smoothVanishingIdeal_iff.1 (hf i)), smul_comm]
    | zero => simp
    | add t u _ _ ht hu =>
      intro g
      rw [smul_add, ← jetLinearMap_apply, map_add, jetLinearMap_apply, jetLinearMap_apply]
      exact add_mem (ht g) (hu g)
    | smul c t _ ht =>
      intro g
      rw [smul_smul]
      exact ht (g * c)
  · rintro _ ⟨ξ, v, rfl⟩
    exact truncate_jetSymbol x ξ v

end JetBundle

/-! ### Jet factors on jets of top order -/

open JetBundle

/-- **The jet factor on jets of top order is the commutator symbol.** For a differential operator
`P` of order at most `r`, its jet factor at `x` sends the value of the symbol of the jet
prolongation at `(ξ₁, …, ξᵣ)` and `v` to the value of the commutator symbol of `P`. Both are
`(P (f₁ ⋯ fᵣ • s))(x)` for functions `fᵢ` vanishing at `x` with `dfᵢ(x) = ξᵢ` and a section `s`
with `s(x) = v`. -/
theorem _root_.LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M)
    (ξ : Fin r → TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    P.jetFactorOfMemDifferentialOperators hP x (jetSymbol I F V r x ξ v) =
      sectionCommutatorSymbol I BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ v := by
  obtain ⟨f, s, hf, rfl, rfl⟩ := exists_mvfderiv_eq_and_apply_eq (F := F) x ξ v
  rw [jetSymbol_mvfderiv hf, LinearMap.jetFactorOfMemDifferentialOperators_jet,
    sectionCommutatorSymbol_mvfderiv_of_forall_apply_eq_zero _ _ hf]

/-- **The principal symbol through jets.** For a differential operator `P` of order at most `r`,
its jet factor at `x` sends the value of the symbol of the jet prolongation at `(ξ, …, ξ)` and `v`
to `r! σ(P)(ξ) v`, where `σ(P)` is the principal symbol. -/
theorem _root_.LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol_const
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    P.jetFactorOfMemDifferentialOperators hP x (jetSymbol I F V r x (fun _ ↦ ξ) v) =
      (r.factorial : ℝ) •
        sectionPrincipalSymbol I BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ v := by
  rw [LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol, sectionPrincipalSymbol_def,
    LinearMap.smul_apply, smul_inv_smul₀ (by exact_mod_cast r.factorial_ne_zero)]

/-- **The jet factor of an operator of lower order.** For `r' ≤ r`, the jet factor at `x` of order
`r` of a differential operator of order at most `r'` is its jet factor of order `r'` composed with
the truncation of `r`-jets to `r'`-jets. -/
theorem _root_.LinearMap.jetFactorOfMemDifferentialOperators_eq_comp_truncate {r' : ℕ}
    (hr : r' ≤ r) {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r')
    (hP' : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ r)
    (x : M) :
    P.jetFactorOfMemDifferentialOperators hP' x =
      P.jetFactorOfMemDifferentialOperators hP x ∘ₗ (truncate hr x).toLinearMap :=
  (LinearMap.eq_jetFactorOfMemDifferentialOperators hP' fun s ↦ by
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, truncate_jet,
      LinearMap.jetFactorOfMemDifferentialOperators_jet]).symm

/-- **Vanishing of the commutator symbol through jets.** An operator of order at most `k + 1` has
vanishing commutator symbol at `x` if and only if its jet factor at `x` kills the jets of order
`k + 1` with vanishing truncation to `k`-jets. -/
theorem sectionCommutatorSymbol_eq_zero_iff_ker_truncate_le {k : ℕ}
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (k + 1))
    (x : M) :
    sectionCommutatorSymbol I (BoundarylessManifold.isInteriorPoint (x := x)) ⟨P, hP⟩ = 0 ↔
      LinearMap.ker
          (truncate (I := I) (F := F) (V := V) (Nat.le_add_right k 1) x).toLinearMap ≤
        LinearMap.ker (P.jetFactorOfMemDifferentialOperators hP x) := by
  constructor
  · intro h
    rw [ker_truncate_eq_span_jetSymbol, Submodule.span_le]
    rintro _ ⟨ξ, v, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol,
      h]
    simp
  · intro h
    ext ξ v
    rw [← LinearMap.jetFactorOfMemDifferentialOperators_jetSymbol]
    exact h (truncate_jetSymbol x ξ v)

/-- **The order filtration through truncation of jets.** For a smooth real vector bundle `W`, an
operator of order at most `k + 1` has order at most `k` if and only if at every point its jet
factor kills the jets of order `k + 1` with vanishing truncation to `k`-jets, that is, factors
through the truncation to `k`-jets. -/
theorem mem_differentialOperators_iff_forall_ker_truncate_le {k : ℕ}
    {P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯}
    (hP : P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ (k + 1)) :
    P ∈ differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ k ↔
      ∀ x, LinearMap.ker
          (truncate (I := I) (F := F) (V := V) (Nat.le_add_right k 1) x).toLinearMap ≤
        LinearMap.ker (P.jetFactorOfMemDifferentialOperators hP x) := by
  rw [← forall_sectionCommutatorSymbol_eq_zero_iff ⟨P, hP⟩]
  exact forall_congr' fun x ↦ sectionCommutatorSymbol_eq_zero_iff_ker_truncate_le hP x

/-! ### The principal symbol on the top-order jets `ofTop` -/

section OfTop

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] {x : M}

/-- **The commutator symbol through jets.** The commutator symbol of a differential operator `P`
of order at most `m` at `(ξ₁, …, ξₘ)`, applied to `v`, is its jet factor at `x` applied to the
top-order jet `ofTop (m! • (ξ₁ ⊗ ⋯ ⊗ ξₘ ⊗ v))`, where `ξ₁ ⊗ ⋯ ⊗ ξₘ ⊗ v` is the multilinear map
`(v₁, …, vₘ) ↦ ξ₁(v₁) ⋯ ξₘ(vₘ) v`. -/
theorem sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionCommutatorSymbol I hx P ξ v =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).jetFactorOfMemDifferentialOperators P.property x
        (ofTop I F V m x (m.factorial •
          (ContinuousMultilinearMap.mkPiRing ℝ (Fin m) v).compContinuousLinearMap ξ)) := by
  -- Lift the covectors to functions `fᵢ` vanishing at `x`, and `v` to a section `s`.
  obtain ⟨f, s, hf, rfl, rfl⟩ := exists_mvfderiv_eq_and_apply_eq (F := F) x ξ v
  have hprod : ⇑((∏ i, f i) • s) = fun y ↦ (∏ i, f i y) • s y := by
    rw [ContMDiffSection.coe_smul_contMDiffMap]
    funext y
    simp only [Pi.smul_apply', ← ContMDiffMap.evalAlgHom_apply (𝕜 := ℝ), map_prod]
  rw [sectionCommutatorSymbol_mvfderiv_of_forall_apply_eq_zero hx P hf s,
    ← LinearMap.jetFactorOfMemDifferentialOperators_jet P.property, hprod, jet_prod_smul f hf s]

/-- **The principal symbol through jets.** The principal symbol `σ(P)(ξ)` of a differential operator
`P` of order at most `m`, applied to `v`, is its jet factor at `x` applied to the top-order jet
`ofTop (ξ ⊗ ⋯ ⊗ ξ ⊗ v)`, where `ξ ⊗ ⋯ ⊗ ξ ⊗ v` is the multilinear map
`(v₁, …, vₘ) ↦ ξ(v₁) ⋯ ξ(vₘ) v`. The principal symbol is the top-order part of the factorization of
`P` through jets. -/
theorem sectionPrincipalSymbol_apply_eq_jetFactorOfMemDifferentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I hx P ξ v =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).jetFactorOfMemDifferentialOperators P.property x
        (ofTop I F V m x
          ((ContinuousMultilinearMap.mkPiRing ℝ (Fin m) v).compContinuousLinearMap fun _ ↦ ξ)) := by
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 m.factorial_ne_zero
  rw [sectionPrincipalSymbol_def, LinearMap.smul_apply,
    sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators, map_nsmul, map_nsmul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm, one_smul]

end OfTop

end TauCeti
