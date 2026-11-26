/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Normed.Operator.CompactFamily
import TauCeti.Analysis.Pseudodifferential.Symbol.Map
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Geometry.Manifold.Diffeomorph.InnerProductSpace

/-!
# Pullback of symbols along diffeomorphisms

A diffeomorphism `κ` of `ℝⁿ` acts on covectors: its *cotangent map* at `x` sends a covector `ξ` at
`x` to the covector `η = (Dκ(x)ᵀ)⁻¹ ξ` at `κ x`, characterized by `⟪η, Dκ(x) v⟫ = ⟪ξ, v⟫` for every
tangent vector `v`. In this file `(Dκ(x)ᵀ)⁻¹` appears as the adjoint of `D(κ⁻¹)(κ x)`. The
*pullback* of a symbol `a(y, η)` along `κ` is its composition with the cotangent map,

`κ^* a (x, ξ) = a(κ x, (Dκ(x)ᵀ)⁻¹ ξ)`.

If `a` is the symbol of a pseudodifferential operator `P` acting on functions of `y = κ x`, then
`κ^* a` is the leading part of the symbol of the transported operator `u ↦ P (u ∘ κ⁻¹) ∘ κ`, whose
full symbol differs from it by terms of lower order (Hörmander, Theorem 18.1.17). This file shows
that the pullback preserves each class of symbols in the calculus:

* `TauCeti.Symbol.pullback`: a symbol of order `m` pulls back to a symbol of order `m`, with no
  assumption on the growth of the derivatives of `κ`, since symbol estimates are only required on
  compact sets of positions. Pullback preserves compact spatial support and smoothing symbols,
  commutes with the inclusions of orders and with pointwise composition, and is functorial
  (`TauCeti.Symbol.pullback_refl`, `TauCeti.Symbol.pullback_trans`).
* `TauCeti.HomogeneousSymbol.pullback`: a homogeneous symbol of degree `m` pulls back to one of
  the same degree, along any diffeomorphism between complete real inner product spaces; it is
  elliptic exactly when the original one is (`TauCeti.HomogeneousSymbol.isElliptic_pullback_iff`).
* `TauCeti.ClassicalSymbol.pullback`: a classical symbol pulls back to a classical symbol whose
  homogeneous terms are the pullbacks of its terms. In particular **the principal symbol transforms
  by the cotangent map** (`TauCeti.ClassicalSymbol.principal_pullback`), and ellipticity is
  invariant under changes of coordinates (`TauCeti.ClassicalSymbol.isElliptic_pullback_iff`).

## Proof outline

Write `L(y)` for the cotangent map at `κ⁻¹ y`, so that `κ^* a (x, ξ) = a(κ x, L(κ x) ξ)`. With
`η = L(y) ξ`, the chain rule expresses each coordinate derivative of `κ^* a` as the pullback of a
symbol built from `a` with the order of the corresponding derivative of `a`:

* `∂_{ξ_j} (κ^* a) = κ^* (∑ₖ (L(y) e_j)ₖ ∂_{η_k} a)`, of order `m - 1`;
* `∂_{x_j} (κ^* a) = κ^* (∑ᵢ vᵢ ∂_{y_i} a + ∑ₖ (DL(y)(v) L(y)⁻¹ η)ₖ ∂_{η_k} a)` with
  `v = Dκ(κ⁻¹ y) e_j`, of order `m`: the factor `ηₖ` costs one order and `∂_{η_k}` gains it back.

The coefficients are smooth functions of `y`, which is why `κ` has to be a diffeomorphism. On a
compact set of positions the cotangent map and its inverse are bounded, so `⟨L(κ x) ξ⟩` and `⟨ξ⟩`
are comparable and `κ^* a` has size `C ⟨ξ⟩ ^ m`. An induction on the number of derivatives then
gives every symbol estimate (`TauCeti.Symbol.exists_norm_mixedDeriv_le_of_deriv_eq`).

For classical symbols the cut-off terms `χ(ξ) a_{m-j}(x, ξ)` pull back to
`χ(L(κ x) ξ) a_{m-j}(κ x, L(κ x) ξ)`, which differ from the cut-off pulled back terms by symbols
vanishing at all frequencies beyond a radius depending on the compact set of positions; these are
smoothing (`TauCeti.Symbol.isSmoothing_of_forall_isCompact_coefficient_eq_zero`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, §8.
-/

public section

noncomputable section

open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### An auxiliary operation -/

private theorem contDiff_apply_apply
    {f : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n} (hf : ContDiff ℝ ∞ f)
    (v : CoordinateSpace n) (k : Fin n) : ContDiff ℝ ∞ fun y ↦ f y v k :=
  (contDiff_piLp 2).1 (hf.clm_apply contDiff_const) k

/-- The derivative `∑ₖ (N(x) ξ)ₖ ∂_{ξₖ} a(x, ξ)` of a symbol in the frequency along `N(x) ξ`, for a
smooth family `N(x)` of linear maps, a symbol of the order of `a`. -/
private def eulerTerm (N : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (hN : ContDiff ℝ ∞ N) (a : Symbol n V W m) : Symbol n V W m :=
  ∑ k, ∑ l, smulLeft
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply hN (EuclideanSpace.single l 1) k))
    (inclusion (by linarith) ((ofInner (EuclideanSpace.single l 1)).comp (frequencyDeriv k a)))

private theorem coefficient_eulerTerm
    (N : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n) (hN : ContDiff ℝ ∞ N)
    (a : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (eulerTerm N hN a).coefficient (x, ξ) =
      ∑ k, N x ξ k • (frequencyDeriv k a).coefficient (x, ξ) := by
  simp only [eulerTerm, coefficient_sum, Finset.sum_apply, coefficient_smulLeft_ofReal,
    coefficient_inclusion, coefficient_comp, coefficient_ofInner, Complex.coe_smul,
    EuclideanSpace.inner_single_right]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h : N x ξ k = ∑ l, ξ l * N x (EuclideanSpace.single l 1) k := by
    rw [(N x).apply_eq_sum_single ξ]
    simp
  simp [h, Finset.sum_smul, smul_smul, mul_comm]

/-! ### Symbol estimates from derivative rules -/

/-- Let `F a` be a family of smooth functions of the position and the frequency, indexed by the
symbols `a` of every order, whose coordinate derivatives are again members of the family:
`∂_{x_j} (F a) = F (S j a)` with `S j a` of the order of `a`, and `∂_{ξ_j} (F a) = F (T j a)` with
`T j a` of one order less. If every member satisfies the order-`m` bound `C ⟨ξ⟩ ^ m` on compact
sets of positions, then every member satisfies all symbol estimates of its order. -/
theorem exists_norm_mixedDeriv_le_of_deriv_eq
    (F : ∀ {m : ℝ}, Symbol n V W m → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
    (S : ∀ {m : ℝ}, Fin n → Symbol n V W m → Symbol n V W m)
    (T : ∀ {m : ℝ}, Fin n → Symbol n V W m → Symbol n V W (m - 1))
    (hF : ∀ {m : ℝ} (a : Symbol n V W m), ContDiff ℝ ∞ (F a))
    (hS : ∀ {m : ℝ} (a : Symbol n V W m) (j : Fin n) (x ξ : CoordinateSpace n),
      coordinateDeriv [j] (fun y ↦ F a (y, ξ)) x = F (S j a) (x, ξ))
    (hT : ∀ {m : ℝ} (a : Symbol n V W m) (j : Fin n) (x ξ : CoordinateSpace n),
      coordinateDeriv [j] (fun η ↦ F a (x, η)) ξ = F (T j a) (x, ξ))
    (hbound : ∀ {m : ℝ} (a : Symbol n V W m) {K : Set (CoordinateSpace n)}, IsCompact K →
      ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖F a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (a : Symbol n V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (F a) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := hbound a hK
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ D ih =>
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C, hC0, hC⟩ := ih (S j a) α' [] (by simpa using hD)
        refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ F a (y, q.2)) q.1) = F (S j a) :=
          funext fun q ↦ hS a j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst (hF a), hfun]
        exact hC x hx ξ
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C, hC0, hC⟩ := ih (T j a) α β' hlen
      refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ F a (q.1, η)) q.2) = F (T j a) :=
        funext fun q ↦ hT a j q.1 q.2
      rw [← mixedDeriv_coordinateDeriv_snd, hfun, ← order_sub_one_sub_length]
      exact hC x hx ξ

/-! ### Composition with a position-dependent change of frequency -/

section Core

variable (κ : CoordinateSpace n ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯
    CoordinateSpace n)
  {L Linv : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n}

/-- The coefficient `a(κ x, L(κ x) ξ)`. -/
private def coreCoeff (L : CoordinateSpace n → CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] W :=
  a.coefficient (κ p.1, L (κ p.1) p.2)

private theorem contDiff_coreCoeff (hL : ContDiff ℝ ∞ L) (a : Symbol n V W m) :
    ContDiff ℝ ∞ (coreCoeff κ L a) :=
  a.contDiff_coefficient.comp ((κ.contDiff.comp contDiff_fst).prodMk
    ((hL.comp (κ.contDiff.comp contDiff_fst)).clm_apply contDiff_snd))

/-- The symbol whose coefficient composed with `(κ x, L(κ x) ξ)` is the position derivative
`∂_{x_j}` of `a(κ x, L(κ x) ξ)`: with `y = κ x`, `η = L(y) ξ` and `v = Dκ(x) e_j`, it is
`∑ᵢ vᵢ ∂_{y_i} a(y, η) + ∑ₖ (DL(y)(v) L(y)⁻¹ η)ₖ ∂_{η_k} a(y, η)`. -/
private def coreSpatial (hL : ContDiff ℝ ∞ L) (hLinv : ContDiff ℝ ∞ Linv) (j : Fin n)
    (a : Symbol n V W m) : Symbol n V W m :=
  (∑ i, smulLeft (Complex.ofRealCLM.contDiff.comp ((contDiff_piLp 2).1
      ((κ.contDiff_fderiv_comp_symm (m := ∞) le_rfl).clm_apply
        (contDiff_const (c := EuclideanSpace.single j 1))) i)) (spatialDeriv i a)) +
    eulerTerm (fun y ↦ (fderiv ℝ L y (fderiv ℝ κ (κ.symm y) (EuclideanSpace.single j 1))).comp
      (Linv y)) (((hL.fderiv_right (m := ∞) le_rfl).clm_apply
        ((κ.contDiff_fderiv_comp_symm (m := ∞) le_rfl).clm_apply contDiff_const)).clm_comp hLinv) a

/-- The symbol whose coefficient composed with `(κ x, L(κ x) ξ)` is the frequency derivative
`∂_{ξ_j}` of `a(κ x, L(κ x) ξ)`, namely `∑ₖ (L(y) e_j)ₖ ∂_{η_k} a(y, L(y) ξ)` at `y = κ x`. -/
private def coreFrequency (hL : ContDiff ℝ ∞ L) (j : Fin n) (a : Symbol n V W m) :
    Symbol n V W (m - 1) :=
  ∑ k, smulLeft
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply_apply hL (EuclideanSpace.single j 1) k))
    (frequencyDeriv k a)

variable {κ}

private theorem coordinateDeriv_coreCoeff_fst (hL : ContDiff ℝ ∞ L) (hLinv : ContDiff ℝ ∞ Linv)
    (hLL : ∀ y, (Linv y).comp (L y) = ContinuousLinearMap.id ℝ _) (a : Symbol n V W m)
    (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ coreCoeff κ L a (y, ξ)) x =
      coreCoeff κ L (coreSpatial κ hL hLinv j a) (x, ξ) := by
  have hκ : HasFDerivAt κ (fderiv ℝ κ x) x :=
    (κ.contDiff.differentiable (by simp) x).hasFDerivAt
  have hLκ : HasFDerivAt (fun x ↦ L (κ x)) ((fderiv ℝ L (κ x)).comp (fderiv ℝ κ x)) x :=
    (hL.differentiable (by simp) _).hasFDerivAt.comp x hκ
  have hη : HasFDerivAt (fun x ↦ L (κ x) ξ) (((fderiv ℝ L (κ x)).comp (fderiv ℝ κ x)).flip ξ) x :=
    by simpa using hLκ.clm_apply (hasFDerivAt_const ξ x)
  have ha := a.contDiff_coefficient.differentiable (by simp) (κ x, L (κ x) ξ)
  have h : HasFDerivAt (fun y ↦ a.coefficient (κ y, L (κ y) ξ)) _ x :=
    ha.hasFDerivAt.comp x (hκ.prodMk hη)
  simp only [coordinateDeriv_cons, coordinateDeriv_nil, coreCoeff]
  rw [h.fderiv, ContinuousLinearMap.comp_apply, fderiv_apply_eq_sum_coordinateDeriv ha]
  have hξ : Linv (κ x) (L (κ x) ξ) = ξ := DFunLike.congr_fun (hLL _) _
  simp only [coreSpatial, coefficient_add, Pi.add_apply, coefficient_sum, Finset.sum_apply]
  rw [coefficient_eulerTerm]
  simp [coefficient_spatialDeriv, coefficient_frequencyDeriv, hξ]

private theorem coordinateDeriv_coreCoeff_snd (hL : ContDiff ℝ ∞ L) (a : Symbol n V W m)
    (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun η ↦ coreCoeff κ L a (x, η)) ξ =
      coreCoeff κ L (coreFrequency hL j a) (x, ξ) := by
  have hη : HasFDerivAt (fun η ↦ (κ x, L (κ x) η))
      ((0 : CoordinateSpace n →L[ℝ] CoordinateSpace n).prod (L (κ x))) ξ :=
    (hasFDerivAt_const _ ξ).prodMk (L (κ x)).hasFDerivAt
  have ha := a.contDiff_coefficient.differentiable (by simp) (κ x, L (κ x) ξ)
  have h : HasFDerivAt (fun η ↦ a.coefficient (κ x, L (κ x) η)) _ ξ := ha.hasFDerivAt.comp ξ hη
  simp only [coordinateDeriv_cons, coordinateDeriv_nil, coreCoeff]
  rw [h.fderiv, ContinuousLinearMap.comp_apply, fderiv_apply_eq_sum_coordinateDeriv ha]
  simp [coreFrequency, coefficient_sum, coefficient_frequencyDeriv]

/-- On a compact set of positions, `a(κ x, L(κ x) ξ)` is bounded by `C ⟨ξ⟩ ^ m`: on the compact set
`κ '' K` the norms of `L` and of its left inverse are bounded, so `⟨L(κ x) ξ⟩` and `⟨ξ⟩` are
comparable. -/
private theorem exists_norm_coreCoeff_le (hL : ContDiff ℝ ∞ L) (hLinv : ContDiff ℝ ∞ Linv)
    (hLL : ∀ y, (Linv y).comp (L y) = ContinuousLinearMap.id ℝ _) (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖coreCoeff κ L a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  have hK' := hK.image κ.continuous
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient _ hK'
  obtain ⟨c, hc, hcK⟩ :=
    hK'.exists_norm_apply_le_and_norm_le hL.continuous.continuousOn hLinv.continuous.continuousOn
      fun y _ ↦ hLL y
  refine ⟨C * c ^ |m|, by positivity, fun x hx ξ ↦ ?_⟩
  have hy : κ x ∈ κ '' K := Set.mem_image_of_mem _ hx
  obtain ⟨h₁, h₂⟩ := hcK _ hy ξ
  calc ‖coreCoeff κ L a (x, ξ)‖ ≤ C * (1 + ‖L (κ x) ξ‖ ^ 2) ^ (m / 2) := hC _ hy _
    _ ≤ C * (c ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :=
      mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_le_of_norm_le_mul hc m h₁ h₂) hC0
    _ = C * c ^ |m| * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring

variable (κ) in
/-- The symbol `a(κ x, L(κ x) ξ)` of order `m`, for a diffeomorphism `κ` and a smooth family of
linear maps `L(y)` with a smooth family of left inverses. -/
private def pullbackCore (hL : ContDiff ℝ ∞ L) (hLinv : ContDiff ℝ ∞ Linv)
    (hLL : ∀ y, (Linv y).comp (L y) = ContinuousLinearMap.id ℝ _) (a : Symbol n V W m) :
    Symbol n V W m where
  coefficient := coreCoeff κ L a
  contDiff_coefficient := contDiff_coreCoeff κ hL a
  exists_bound _ hK α β := exists_norm_mixedDeriv_le_of_deriv_eq (fun a ↦ coreCoeff κ L a)
    (fun j a ↦ coreSpatial κ hL hLinv j a) (fun j a ↦ coreFrequency hL j a)
    (fun a ↦ contDiff_coreCoeff κ hL a) (coordinateDeriv_coreCoeff_fst hL hLinv hLL)
    (coordinateDeriv_coreCoeff_snd hL) (fun a _ hK ↦ exists_norm_coreCoeff_le hL hLinv hLL a hK)
    a hK α β

end Core

/-! ### Pullback along a diffeomorphism -/

section Pullback

variable (κ : CoordinateSpace n ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯
  CoordinateSpace n)

/-- **The pullback of a symbol along a diffeomorphism** `κ` of `ℝⁿ`: the symbol
`(x, ξ) ↦ a(κ x, (Dκ(x)ᵀ)⁻¹ ξ)` of the same order. It is `a` composed with the map of the cotangent
bundle that `κ` induces, which sends a covector `ξ` at `x` to the covector `η` at `κ x` with
`⟪η, Dκ(x) v⟫ = ⟪ξ, v⟫` for every tangent vector `v`. In the formula `(Dκ(x)ᵀ)⁻¹` is written as
the adjoint of `D(κ⁻¹)(κ x)` (`TauCeti.Symbol.coefficient_pullback`).

If `a` is the symbol of an operator `P` on functions of `y = κ x`, its pullback is the leading part
of the symbol of the transported operator `u ↦ P (u ∘ κ⁻¹) ∘ κ`; the transformation rule of the
principal symbol (`TauCeti.ClassicalSymbol.principal_pullback`) is the case of homogeneous
terms. -/
def pullback : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a := pullbackCore κ (κ.contDiff_adjoint_fderiv_symm le_rfl)
    (κ.contDiff_adjoint_fderiv_comp_symm le_rfl)
    (κ.adjoint_fderiv_comp_adjoint_fderiv_symm (by simp)) a
  map_add' _ _ := Symbol.ext (funext fun _ ↦ by simp [pullbackCore, coreCoeff])
  map_smul' _ _ := Symbol.ext (funext fun _ ↦ by simp [pullbackCore, coreCoeff])

variable {κ}

@[simp]
theorem coefficient_pullback (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (pullback κ a).coefficient p =
      a.coefficient (κ p.1, ContinuousLinearMap.adjoint (fderiv ℝ κ.symm (κ p.1)) p.2) :=
  (rfl)

@[simp]
theorem pullback_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    pullback κ (inclusion h a) = inclusion h (pullback κ a) :=
  Symbol.ext (funext fun _ ↦ by simp)

@[simp]
theorem pullback_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (b : Symbol n W U m') (a : Symbol n V W m) :
    pullback κ (b.comp a) = (pullback κ b).comp (pullback κ a) :=
  Symbol.ext (funext fun _ ↦ by simp [coefficient_comp])

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem pullback_refl (a : Symbol n V W m) :
    pullback (Diffeomorph.refl 𝓘(ℝ, CoordinateSpace n) (CoordinateSpace n) ∞) a = a :=
  Symbol.ext (funext fun _ ↦ by simp [Diffeomorph.coe_refl, ContinuousLinearMap.adjoint_id])

/-- **Functoriality**: pulling back along `κ₂ ∘ κ₁` is pulling back along `κ₂`, then along `κ₁`. -/
@[simp]
theorem pullback_trans
    (κ₁ κ₂ : CoordinateSpace n ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯
      CoordinateSpace n) (a : Symbol n V W m) :
    pullback (κ₁.trans κ₂) a = pullback κ₁ (pullback κ₂ a) :=
  Symbol.ext (funext fun p ↦ by
    rw [coefficient_pullback, Diffeomorph.adjoint_fderiv_trans_symm _ _ (by simp)]
    simp [Diffeomorph.coe_trans])

theorem HasCompactSpatialSupport.pullback {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) :
    (pullback κ a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2 ⟨κ.symm '' K, hK.image κ.symm.continuous, fun x hx ξ ↦ ?_⟩
  rw [coefficient_pullback]
  exact hKa _ (fun h ↦ hx ⟨κ x, h, κ.symm_apply_apply x⟩) _

theorem IsSmoothing.pullback {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (pullback κ a).IsSmoothing := isSmoothing_iff.2 fun m' ↦ by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.pullback κ b, funext fun _ ↦ by simp [hb]⟩

end Pullback

end Symbol

namespace HomogeneousSymbol

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {m : ℝ} (κ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F)

/-- **The pullback of a homogeneous symbol along a diffeomorphism** `κ`: the homogeneous symbol
`(x, ξ) ↦ a(κ x, (Dκ(x)ᵀ)⁻¹ ξ)` of the same degree, the composition of `a` with the map of the
cotangent bundle induced by `κ`. Since this map is linear and injective on each fibre, it
preserves homogeneity and the smoothness away from the zero covector. -/
def pullback : HomogeneousSymbol F F V W m →ₗ[ℂ] HomogeneousSymbol E E V W m where
  toFun a :=
    { coefficient p :=
        a.coefficient (κ p.1, ContinuousLinearMap.adjoint (fderiv ℝ κ.symm (κ p.1)) p.2)
      zero_covector x := by simp
      contDiffOn_coefficient := a.contDiffOn_coefficient.comp
        ((κ.contDiff.comp contDiff_fst).prodMk (((κ.contDiff_adjoint_fderiv_symm le_rfl).comp
          (κ.contDiff.comp contDiff_fst)).clm_apply contDiff_snd)).contDiffOn
        fun _ hp ↦ κ.adjoint_fderiv_symm_apply_ne_zero (by simp) hp
      homogeneous x ξ t ht := by simp [a.homogeneous _ _ t ht] }
  map_add' _ _ := HomogeneousSymbol.ext (funext fun _ ↦ by simp)
  map_smul' _ _ := HomogeneousSymbol.ext (funext fun _ ↦ by simp)

variable {κ}

@[simp]
theorem coefficient_pullback (a : HomogeneousSymbol F F V W m) (p : E × E) :
    (pullback κ a).coefficient p =
      a.coefficient (κ p.1, ContinuousLinearMap.adjoint (fderiv ℝ κ.symm (κ p.1)) p.2) :=
  (rfl)

@[simp]
theorem pullback_castDegree {m' : ℝ} (h : m = m') (a : HomogeneousSymbol F F V W m) :
    pullback κ (a.castDegree h) = (pullback κ a).castDegree h :=
  HomogeneousSymbol.ext (funext fun _ ↦ by simp)

@[simp]
theorem pullback_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (b : HomogeneousSymbol F F W U m') (a : HomogeneousSymbol F F V W m) :
    pullback κ (b.comp a) = (pullback κ b).comp (pullback κ a) :=
  HomogeneousSymbol.ext (funext fun _ ↦ by simp)

@[simp]
theorem pullback_refl (a : HomogeneousSymbol E E V W m) :
    pullback (Diffeomorph.refl 𝓘(ℝ, E) E ∞) a = a :=
  HomogeneousSymbol.ext
    (funext fun _ ↦ by simp [Diffeomorph.coe_refl, ContinuousLinearMap.adjoint_id])

@[simp]
theorem pullback_trans (κ₁ : E ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F) (κ₂ : F ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ G)
    (a : HomogeneousSymbol G G V W m) :
    pullback (κ₁.trans κ₂) a = pullback κ₁ (pullback κ₂ a) :=
  HomogeneousSymbol.ext (funext fun p ↦ by
    rw [coefficient_pullback, Diffeomorph.adjoint_fderiv_trans_symm _ _ (by simp)]
    simp [Diffeomorph.coe_trans])

/-- A homogeneous symbol is elliptic exactly when its pullback along a diffeomorphism is: the
cotangent map of `κ` is a bijection of the nonzero covectors over each point. -/
@[simp]
theorem isElliptic_pullback_iff {a : HomogeneousSymbol F F V W m} :
    (pullback κ a).IsElliptic ↔ a.IsElliptic := by
  simp only [isElliptic_iff, coefficient_pullback]
  refine ⟨fun h y η hη ↦ ?_, fun h x ξ hξ ↦
    h _ _ (κ.adjoint_fderiv_symm_apply_ne_zero (by simp) hξ)⟩
  -- Write `y = κ x` and `η` as the image of `ξ = Dκ(x)ᵀ η` under the cotangent map at `x`.
  obtain ⟨x, rfl⟩ : ∃ x, κ x = y := ⟨κ.symm y, κ.apply_symm_apply y⟩
  have hξ : ContinuousLinearMap.adjoint (fderiv ℝ κ x) η ≠ 0 := fun h0 ↦
    hη (by simpa [h0] using (κ.adjoint_fderiv_symm_adjoint_fderiv_apply (by simp) x η).symm)
  simpa using h x _ hξ

end HomogeneousSymbol

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}
  (κ : CoordinateSpace n ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯
    CoordinateSpace n)

open HomogeneousSymbol in
/-- Pulling back a cut-off homogeneous term `χ(ξ) h(x, ξ)` along `κ` gives the cut-off pulled back
term `χ(ξ) h(κ x, (Dκ(x)ᵀ)⁻¹ ξ)` up to a smoothing symbol: on a compact set of positions the
cotangent map of `κ` is bounded below, so both cutoffs equal `1` at all large frequencies. -/
private theorem isSmoothing_pullback_cutoffSymbol_sub (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (Symbol.pullback κ (cutoffSymbol χ h) -
      cutoffSymbol χ (HomogeneousSymbol.pullback κ h)).IsSmoothing := by
  refine Symbol.isSmoothing_of_forall_isCompact_coefficient_eq_zero fun K hK ↦ ?_
  obtain ⟨c, hc, hcK⟩ := (hK.image κ.continuous).exists_norm_apply_le_and_norm_le
    (κ.contDiff_adjoint_fderiv_symm (m := 0) (by simp)).continuous.continuousOn
    (κ.contDiff_adjoint_fderiv_comp_symm (m := 0) (by simp)).continuous.continuousOn
    fun y _ ↦ κ.adjoint_fderiv_comp_adjoint_fderiv_symm (by simp) y
  refine ⟨2 * c, fun x hx ξ hξ ↦ ?_⟩
  set η := ContinuousLinearMap.adjoint (fderiv ℝ κ.symm (κ x)) ξ
  have hξη : ‖ξ‖ ≤ c * ‖η‖ := (hcK _ (Set.mem_image_of_mem _ hx) ξ).2
  have h2ξ : 2 ≤ ‖ξ‖ := le_trans (by linarith) hξ
  have h2η : 2 ≤ ‖η‖ := le_of_mul_le_mul_left (by linarith) (by linarith : 0 < c)
  simp [Symbol.coefficient_sub, χ.apply_eq_one_of_two_le_norm h2ξ,
    χ.apply_eq_one_of_two_le_norm h2η, η]

/-- **The pullback of a classical symbol along a diffeomorphism** `κ`: the full symbol
`a(κ x, (Dκ(x)ᵀ)⁻¹ ξ)` (`TauCeti.Symbol.pullback`) is classical, with homogeneous terms the
pullbacks of the terms of `a`. Changing the cutoff `χ(ξ)` of the expansion to `χ((Dκ(x)ᵀ)⁻¹ ξ)`
costs only smoothing symbols. -/
def pullback : ClassicalSymbol n V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun a :=
    { toSymbol := Symbol.pullback κ a.toSymbol
      term j := HomogeneousSymbol.pullback κ (a.term j)
      exists_remainder' := by
        obtain ⟨χ, -⟩ := a.exists_remainder'
        refine ⟨χ, fun N ↦ ?_⟩
        -- The pulled back remainder after `N` terms, corrected by the smoothing differences of the
        -- pulled back cut-off terms and the cut-off pulled back terms.
        let D : Symbol n V W m := ∑ j ∈ Finset.range N,
          Symbol.inclusion (sub_le_self m (Nat.cast_nonneg j))
            (Symbol.pullback κ (HomogeneousSymbol.cutoffSymbol χ (a.term j)) -
              HomogeneousSymbol.cutoffSymbol χ (HomogeneousSymbol.pullback κ (a.term j)))
        have hD : D.IsSmoothing := Finset.sum_induction _ Symbol.IsSmoothing
          (fun _ _ ↦ Symbol.IsSmoothing.add) Symbol.isSmoothing_zero fun j _ ↦
            (isSmoothing_pullback_cutoffSymbol_sub κ χ (a.term j)).inclusion _
        obtain ⟨b, hb⟩ := Symbol.isSmoothing_iff.1 hD (m - N)
        refine ⟨Symbol.pullback κ (a.remainder χ N) + b, fun p ↦ ?_⟩
        simp only [Symbol.coefficient_add, Pi.add_apply, hb, D, Symbol.coefficient_sum,
          Finset.sum_apply, Symbol.coefficient_inclusion, Symbol.coefficient_sub, Pi.sub_apply,
          Symbol.coefficient_pullback, coefficient_remainder,
          HomogeneousSymbol.coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_pullback,
          Finset.sum_sub_distrib]
        abel }
  map_add' _ _ := ClassicalSymbol.ext (by simp)
  map_smul' _ _ := ClassicalSymbol.ext (by simp)

variable {κ}

@[simp]
theorem toSymbol_pullback (a : ClassicalSymbol n V W m) :
    (pullback κ a).toSymbol = Symbol.pullback κ a.toSymbol :=
  (rfl)

@[simp]
theorem term_pullback (a : ClassicalSymbol n V W m) (j : ℕ) :
    (pullback κ a).term j = HomogeneousSymbol.pullback κ (a.term j) :=
  (rfl)

@[simp]
theorem pullback_refl (a : ClassicalSymbol n V W m) :
    pullback (Diffeomorph.refl 𝓘(ℝ, CoordinateSpace n) (CoordinateSpace n) ∞) a = a :=
  ClassicalSymbol.ext (by simp)

@[simp]
theorem pullback_trans
    (κ₁ κ₂ : CoordinateSpace n ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯
      CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    pullback (κ₁.trans κ₂) a = pullback κ₁ (pullback κ₂ a) :=
  ClassicalSymbol.ext (by simp [Symbol.pullback_trans])

@[simp]
theorem pullback_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (b : ClassicalSymbol n W U m') (a : ClassicalSymbol n V W m) :
    pullback κ (b.comp a) = (pullback κ b).comp (pullback κ a) :=
  ClassicalSymbol.ext (by simp [toSymbol_comp, Symbol.pullback_comp])

@[simp]
theorem pullback_inclusion {m' : ℝ} (k : ℕ) (hk : m' = m - k) (b : ClassicalSymbol n V W m') :
    pullback κ (inclusion k hk b) = inclusion k hk (pullback κ b) :=
  ClassicalSymbol.ext (by simp)

@[simp]
theorem pullback_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) :
    pullback κ (ofIsSmoothing a ha) = ofIsSmoothing (Symbol.pullback κ a) ha.pullback :=
  ClassicalSymbol.ext (by simp)

/-- **The principal symbol transforms by the cotangent map**: the principal symbol of the pullback
of a classical symbol along `κ` is `σ(a)(κ x, (Dκ(x)ᵀ)⁻¹ ξ)`. -/
@[simp]
theorem principal_pullback (a : ClassicalSymbol n V W m) :
    (pullback κ a).principal = HomogeneousSymbol.pullback κ a.principal := by
  rw [principal_def, principal_def, term_pullback, HomogeneousSymbol.pullback_castDegree]

/-- Ellipticity is invariant under changes of coordinates. -/
@[simp]
theorem isElliptic_pullback_iff {a : ClassicalSymbol n V W m} :
    (pullback κ a).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_pullback,
    HomogeneousSymbol.isElliptic_pullback_iff]

end ClassicalSymbol

end TauCeti
