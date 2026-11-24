/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Linear changes of coordinates

Let `A` be a linear automorphism of `ℝⁿ` and write `y = A x`. A pseudodifferential operator
`Op(a)` in the coordinates `x` becomes, in the coordinates `y`, the operator
`u ↦ Op(a) (u ∘ A) ∘ A⁻¹`. For a linear change this is again a Kohn–Nirenberg quantization, with no
lower-order corrections: it is `Op(b)` for

`b(y, η) = a(A⁻¹ y, Aᵀ η)`,

where `Aᵀ` is the adjoint of `A`. Positions transform by `A` and frequencies, being covectors, by
the inverse transpose `(Aᵀ)⁻¹`, so the symbol transforms as a function on the cotangent bundle.
For nonlinear changes of coordinates the same holds only up to lower-order terms.

This file proves the exact formula and that the symbol classes are invariant:

* `TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`: for every coefficient `a` on a
  finite-dimensional inner product space, `Op(a) (u ∘ A) (x) = Op(b) u (A x)`. It follows from the
  Fourier change of variables `ContinuousLinearEquiv.fourier_comp` and its inverse-transform
  version.
* `TauCeti.Symbol.compProdMap`: for a linear map `P` of positions and a linear isomorphism `Q` of
  frequencies, `(x, ξ) ↦ a(P x, Q ξ)` is a symbol of order `m` whenever `a` is. It preserves
  uniform estimates, smoothing symbols and, for invertible `P`, compact spatial support.
  `TauCeti.Symbol.quantizeSchwartzValue_compProdMap_symm_adjointEquiv` combines this with the
  formula above: written in linear coordinates, the quantization of a symbol of order `m` is the
  quantization of a symbol of order `m`, and
  `TauCeti.Symbol.quantizeUniformCLM_compProdMap_symm_adjointEquiv` is the same identity for the
  operator on Schwartz space. For invertible `P` the change of variables is injective and the
  symbol classes are invariant in both directions (`TauCeti.Symbol.isUniform_compProdMap_iff` and
  its analogues).
* `TauCeti.Symbol.exists_bound_mixedDeriv_comp_prodMap_of_norm_le_mul_norm`: the estimates for
  `a ∘ (P × Q)` hold with one constant for all `P` and `Q` in a bounded set with `Q⁻¹` bounded
  too, as needed for families of linear changes of variables such as compact group actions.
* `TauCeti.Symbol.compProdMap_symm_adjointEquiv_eq_self_iff`: a pseudodifferential operator
  commutes with the change of coordinates `u ↦ u ∘ A` exactly when its symbol is invariant under
  `(x, ξ) ↦ (A⁻¹ x, Aᵀ ξ)`.
* `TauCeti.ClassicalSymbol.compProdMap`: the same change of variables in a classical symbol, whose
  homogeneous terms transform alike (`TauCeti.HomogeneousSymbol.compProdMap`). In particular the
  principal symbol transforms by the same rule (`TauCeti.ClassicalSymbol.principal_compProdMap`),
  and ellipticity is invariant (`TauCeti.ClassicalSymbol.isElliptic_compProdMap_iff`).

The symbol estimates for `a ∘ (P × Q)` come from the chain rule: a mixed derivative of
`a ∘ (P × Q)` is a derivative of `a` at `(P x, Q ξ)` along the directions `(P eⱼ, 0)` and
`(0, Q eⱼ)` (`TauCeti.mixedDeriv_comp_prodMap`). Expanding these directions in the standard basis
of each factor bounds it by mixed derivatives of `a` with the same numbers of position and
frequency derivatives, with the weight `⟨Q ξ⟩` and one constant for all `P` and `Q` of bounded
norm (`TauCeti.exists_bound_mixedDeriv_comp_prodMap`). The weights `⟨Q ξ⟩` and `⟨ξ⟩` are
comparable since `Q` is invertible.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17,
  the change of variables formula, which has no lower-order terms for linear changes.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

variable {n : ℕ}

namespace Symbol

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-- **Uniform symbol estimates under linear changes of variables.** Let `1 ≤ c`. If a smooth
coefficient `f` satisfies the estimates of order `m` with constants `C α' β'` at the position
`P x`, then `f ∘ (P × Q)` satisfies the estimate of order `m` for `(α, β)` at the position `x`.
The constant `B` depends only on `c`, the constants `C` and `(α, β)`, and serves every pair of
linear maps `P`, `Q` with `‖P‖ ≤ c`, `‖Q‖ ≤ c` and `‖ξ‖ ≤ c ‖Q ξ‖`; the last condition makes
`⟨Q ξ⟩` and `⟨ξ⟩` comparable. -/
theorem exists_bound_mixedDeriv_comp_prodMap_of_norm_le_mul_norm
    {f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} (hf : ContDiff ℝ ∞ f) {c : ℝ}
    (hc : 1 ≤ c) (C : List (Fin n) → List (Fin n) → ℝ) (α β : List (Fin n)) :
    ∃ B, 0 ≤ B ∧ ∀ P Q : CoordinateSpace n →L[ℝ] CoordinateSpace n, ‖P‖ ≤ c → ‖Q‖ ≤ c →
      (∀ ξ, ‖ξ‖ ≤ c * ‖Q ξ‖) → ∀ x, (∀ α' β' η, ‖mixedDeriv α' β' f (P x) η‖ ≤
        C α' β' * (1 + ‖η‖ ^ 2) ^ ((m - β'.length) / 2)) → ∀ ξ,
      ‖mixedDeriv α β (f ∘ P.prodMap Q) x ξ‖ ≤ B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨B, hB, h⟩ := exists_bound_mixedDeriv_comp_prodMap (α := α) (β := β)
    (hf.of_le (mod_cast le_top)) (zero_le_one.trans hc) C m
  refine ⟨B * c ^ |m - β.length|, by positivity, fun P Q hP hQ hQ' x hC ξ =>
    (h P Q hP hQ x hC ξ).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_le_of_norm_le_mul hc _
    ((Q.le_opNorm ξ).trans (by gcongr)) (hQ' ξ)) hB

/-- The symbol estimates of a smooth coefficient `f` at the position `P x` give estimates of
`f ∘ (P × Q)` at the position `x`, with a constant depending only on `P`, `Q` and the constants
for `f`. The frequency map `Q` is invertible, so that `⟨Q ξ⟩` and `⟨ξ⟩` are comparable. -/
private theorem exists_bound_comp_prodMap {f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W}
    (hf : ContDiff ℝ ∞ f) (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (C : List (Fin n) → List (Fin n) → ℝ)
    (α β : List (Fin n)) :
    ∃ B, 0 ≤ B ∧ ∀ x, (∀ α' β' η, ‖mixedDeriv α' β' f (P x) η‖ ≤
        C α' β' * (1 + ‖η‖ ^ 2) ^ ((m - β'.length) / 2)) → ∀ ξ,
      ‖mixedDeriv α β (f ∘ P.prodMap (Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)) x ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set c : ℝ := max 1 (max ‖P‖ (max ‖(Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖
    ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖))
  obtain ⟨B, hB, h⟩ :=
    exists_bound_mixedDeriv_comp_prodMap_of_norm_le_mul_norm (m := m) hf (le_max_left 1 _) C α β
  exact ⟨B, hB, h P Q (le_max_of_le_right (le_max_left _ _))
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    fun ξ => (Q.antilipschitzWith.le_mul_norm (map_zero Q) ξ).trans (mul_le_mul_of_nonneg_right
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))) (norm_nonneg _))⟩

/-- **Linear change of variables in a symbol.** For a linear map `P` of positions and a linear
isomorphism `Q` of frequencies, the symbol `(x, ξ) ↦ a(P x, Q ξ)` of order `m`, as a `ℂ`-linear map
on `Symbol n V W m`. -/
def compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := a.coefficient ∘ P.prodMap (Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      contDiff_coefficient := a.contDiff_coefficient.comp
        (P.prodMap (Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)).contDiff
      exists_bound K hK α β := by
        choose C _ hC using fun α' β' => a.exists_bound (P '' K) (hK.image P.continuous) α' β'
        obtain ⟨B, hB, hB'⟩ := exists_bound_comp_prodMap a.contDiff_coefficient P Q C α β
        exact ⟨B, hB, fun x hx ξ => hB' x (fun α' β' η => hC α' β' (P x) ⟨x, hx, rfl⟩ η) ξ⟩ }
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

@[simp]
theorem coefficient_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (compProdMap P Q a).coefficient p = a.coefficient (P p.1, Q p.2) := (rfl)

/-- The identity change of variables leaves a symbol unchanged. -/
@[simp]
theorem compProdMap_id (a : Symbol n V W m) :
    compProdMap (.id ℝ (CoordinateSpace n)) (.refl ℝ (CoordinateSpace n)) a = a :=
  Symbol.ext (funext fun _ => by simp)

/-- Two successive linear changes of variables compose: first `(P, Q)`, then `(P', Q')`. -/
@[simp]
theorem compProdMap_compProdMap (P P' : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q Q' : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m) :
    compProdMap P' Q' (compProdMap P Q a) = compProdMap (P.comp P') (Q'.trans Q) a :=
  Symbol.ext (funext fun _ => by simp)

/-- The linear change of variables commutes with the inclusion of symbol classes. -/
@[simp]
theorem compProdMap_inclusion (h : m ≤ m') (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m) :
    compProdMap P Q (inclusion h a) = inclusion h (compProdMap P Q a) :=
  Symbol.ext (funext fun _ => by simp)

/-- The linear change of variables commutes with the pointwise composition of symbols. -/
@[simp]
theorem compProdMap_comp (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (b : Symbol n W U m')
    (a : Symbol n V W m) :
    compProdMap P Q (b.comp a) = (compProdMap P Q b).comp (compProdMap P Q a) :=
  Symbol.ext (funext fun _ => by simp)

/-- A linear change of variables preserves estimates uniform in the position. -/
theorem IsUniform.compProdMap {a : Symbol n V W m} (ha : a.IsUniform)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (compProdMap P Q a).IsUniform := by
  rw [isUniform_iff] at ha ⊢
  intro α β
  choose C _ hC using ha
  obtain ⟨B, hB, hB'⟩ := exists_bound_comp_prodMap a.contDiff_coefficient P Q C α β
  exact ⟨B, hB, fun x ξ => hB' x (fun α' β' η => hC α' β' (P x) η) ξ⟩

/-- A linear change of variables preserves smoothing symbols. -/
theorem IsSmoothing.compProdMap {a : Symbol n V W m} (ha : a.IsSmoothing)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (compProdMap P Q a).IsSmoothing := by
  rw [isSmoothing_iff] at ha ⊢
  intro m''
  obtain ⟨b, hb⟩ := ha m''
  exact ⟨Symbol.compProdMap P Q b, funext fun p => by simp [hb]⟩

/-- An invertible linear change of positions preserves compact spatial support: if `a` vanishes
outside `K`, then `(x, ξ) ↦ a(P x, Q ξ)` vanishes outside `P⁻¹ K`. -/
theorem HasCompactSpatialSupport.compProdMap {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (P Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2 ⟨P.symm '' K, hK.image P.symm.continuous, fun x hx ξ => ?_⟩
  rw [coefficient_compProdMap]
  exact hKa _ (fun hPx => hx ⟨P x, hPx, by simp⟩) _

section Invertible

variable (P Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)

/-- An invertible linear change of variables is injective on symbols: it is undone by the change of
variables along `(P⁻¹, Q⁻¹)`. -/
theorem compProdMap_injective :
    Function.Injective
      (compProdMap (V := V) (W := W) (m := m) (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q) :=
  fun a b h => by
    simpa using congrArg
      (compProdMap (P.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q.symm) h

@[simp]
theorem isUniform_compProdMap_iff {a : Symbol n V W m} :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).IsUniform ↔ a.IsUniform :=
  ⟨fun h => by
    simpa using IsUniform.compProdMap h (P.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q.symm,
    fun h => h.compProdMap _ Q⟩

@[simp]
theorem isSmoothing_compProdMap_iff {a : Symbol n V W m} :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).IsSmoothing ↔
      a.IsSmoothing :=
  ⟨fun h => by
    simpa using
      IsSmoothing.compProdMap h (P.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q.symm,
    fun h => h.compProdMap _ Q⟩

@[simp]
theorem hasCompactSpatialSupport_compProdMap_iff {a : Symbol n V W m} :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).HasCompactSpatialSupport ↔
      a.HasCompactSpatialSupport :=
  ⟨fun h => by simpa using h.compProdMap P.symm Q.symm, fun h => h.compProdMap P Q⟩

end Invertible

end Symbol

namespace ClassicalSymbol

variable {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U] {m m' : ℝ}

/-- Cutting off a transformed homogeneous term differs from transforming the cut-off term by a
smoothing symbol: the two agree once both `‖ξ‖` and `‖Q ξ‖` are at least `2`. -/
private theorem isSmoothing_compProdMap_cutoffSymbol_sub
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (χ : FrequencyCutoff (CoordinateSpace n))
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (Symbol.compProdMap P Q (HomogeneousSymbol.cutoffSymbol χ h) -
      HomogeneousSymbol.cutoffSymbol χ (h.compProdMap P Q)).IsSmoothing := by
  set c : ℝ := max 1 ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖
  have hc : 1 ≤ c := le_max_left _ _
  refine Symbol.isSmoothing_of_coefficient_eq_zero (2 * c) fun x ξ hξ => ?_
  have hQ : 2 ≤ ‖Q ξ‖ := by
    have h1 : ‖ξ‖ ≤ c * ‖Q ξ‖ :=
      calc ‖ξ‖ ≤ ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ * ‖Q ξ‖ :=
            Q.antilipschitzWith.le_mul_norm (map_zero Q) ξ
        _ ≤ c * ‖Q ξ‖ := by gcongr; exact le_max_right _ _
    nlinarith
  simp [χ.apply_eq_one_of_two_le_norm hQ,
    χ.apply_eq_one_of_two_le_norm (show 2 ≤ ‖ξ‖ by nlinarith)]

/-- **Linear change of variables in a classical symbol.** For a linear map `P` of positions and a
linear isomorphism `Q` of frequencies, the classical symbol `(x, ξ) ↦ a(P x, Q ξ)` of order `m`,
whose homogeneous terms are those of `a` transformed in the same way, as a `ℂ`-linear map on
`ClassicalSymbol n V W m`. -/
def compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    ClassicalSymbol n V W m →ₗ[ℂ] ClassicalSymbol n V W m where
  toFun a :=
    { toSymbol := Symbol.compProdMap P Q a.toSymbol
      term j := (a.term j).compProdMap P Q
      exists_remainder' := by
        obtain ⟨χ, -⟩ := a.exists_remainder'
        refine ⟨χ, fun N => ?_⟩
        obtain ⟨r, hr⟩ := a.exists_remainder χ N
        choose s hs using fun j => Symbol.isSmoothing_iff.1
          (isSmoothing_compProdMap_cutoffSymbol_sub P Q χ (a.term j)) (m - N)
        refine ⟨Symbol.compProdMap P Q r + ∑ j ∈ Finset.range N, s j, fun p => ?_⟩
        simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum,
          Finset.sum_apply, hs, Symbol.coefficient_compProdMap, hr, Symbol.coefficient_sub,
          Pi.sub_apply, HomogeneousSymbol.coefficient_cutoffSymbol,
          HomogeneousSymbol.coefficient_compProdMap, Finset.sum_sub_distrib]
        abel }
  map_add' a b := ext (map_add (Symbol.compProdMap P Q) a.toSymbol b.toSymbol)
  map_smul' c a := ext (map_smul (Symbol.compProdMap P Q) c a.toSymbol)

@[simp]
theorem toSymbol_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    (compProdMap P Q a).toSymbol = Symbol.compProdMap P Q a.toSymbol := (rfl)

@[simp]
theorem term_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) (j : ℕ) :
    (compProdMap P Q a).term j = (a.term j).compProdMap P Q := (rfl)

/-- The identity change of variables leaves a classical symbol unchanged. -/
@[simp]
theorem compProdMap_id (a : ClassicalSymbol n V W m) :
    compProdMap (.id ℝ (CoordinateSpace n)) (.refl ℝ (CoordinateSpace n)) a = a :=
  ext (by simp)

/-- Two successive linear changes of variables compose: first `(P, Q)`, then `(P', Q')`. -/
@[simp]
theorem compProdMap_compProdMap (P P' : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q Q' : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    compProdMap P' Q' (compProdMap P Q a) = compProdMap (P.comp P') (Q'.trans Q) a :=
  ext (by simp)

/-- The linear change of variables commutes with the inclusion of classical symbol orders. -/
@[simp]
theorem compProdMap_inclusion (k : ℕ) (hk : m' = m - k)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m') :
    compProdMap P Q (inclusion k hk a) = inclusion k hk (compProdMap P Q a) :=
  ext (by simp)

/-- The linear change of variables commutes with the pointwise composition of classical
symbols. -/
@[simp]
theorem compProdMap_comp (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (b : ClassicalSymbol n W U m')
    (a : ClassicalSymbol n V W m) :
    compProdMap P Q (b.comp a) = (compProdMap P Q b).comp (compProdMap P Q a) :=
  ext (by simp)

/-- **The principal symbol commutes with linear changes of variables.** Under the linear change of
variables `(x, ξ) ↦ (P x, Q ξ)`, the principal symbol of the transformed classical symbol is the
transformed principal symbol. -/
@[simp]
theorem principal_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    (compProdMap P Q a).principal = a.principal.compProdMap P Q :=
  HomogeneousSymbol.ext (funext fun p => by simp)

/-- A linear change of variables preserves ellipticity. -/
theorem IsElliptic.compProdMap {a : ClassicalSymbol n V W m} (ha : a.IsElliptic)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (compProdMap P Q a).IsElliptic := by
  rw [isElliptic_def, principal_compProdMap]
  exact (isElliptic_def.1 ha).compProdMap P Q

/-- **Ellipticity is invariant under invertible linear changes of variables.** -/
@[simp]
theorem isElliptic_compProdMap_iff (P Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    {a : ClassicalSymbol n V W m} :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).IsElliptic ↔
      a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_compProdMap,
    HomogeneousSymbol.isElliptic_compProdMap_iff]

end ClassicalSymbol

section Quantization

open scoped FourierTransform SchwartzMap
open MeasureTheory Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {m : ℝ}

/-- **Linear change of coordinates in the quantization.** For a linear automorphism `A`,
`Op(a) (u ∘ A) (x) = Op(b) u (A x)` with `b(y, η) = a(A⁻¹ y, Aᵀ η)`, where `Aᵀ` is the adjoint
of `A`. In the coordinates `y = A x` the operator `Op(a)` is the quantization of `b`: positions
transform by `A` and frequencies, being covectors, by the inverse transpose. This holds exactly,
for every coefficient. -/
theorem quantizeSchwartzValue_compCLMOfContinuousLinearEquiv (a : E × E → V →L[ℂ] W)
    (A : E ≃L[ℝ] E) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (fun p => a (A.symm p.1, A.adjointEquiv p.2)) u (A x) := by
  rw [quantizeSchwartzValue_eq_fourierInv, quantizeSchwartzValue_eq_fourierInv]
  -- Frequencies `ζ` of `u ∘ A` correspond to the frequencies `B ζ` of `u`, `B = (A⁻¹)ᵀ`.
  set B : E ≃L[ℝ] E := A.symm.adjointEquiv
  set h : E → W := fun θ => a (x, A.adjointEquiv ((2 * π) • θ)) (𝓕 u θ)
  have hdetB : (B.toLinearEquiv : E →ₗ[ℝ] E).det = (A.toLinearEquiv : E →ₗ[ℝ] E).det⁻¹ := by
    rw [ContinuousLinearEquiv.det_adjointEquiv, star_trivial,
      ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.det_coe_symm]
  have hfun : (fun ζ => a (x, (2 * π) • ζ)
      (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) ζ)) =
      |(A.toLinearEquiv : E →ₗ[ℝ] E).det|⁻¹ • (h ∘ B) := by
    funext ζ
    have hAB : A.adjointEquiv (B ζ) = ζ := by
      simpa [B] using A.symm.adjointEquiv.symm_apply_apply ζ
    simp only [SchwartzMap.fourier_coe, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      A.fourier_comp, Pi.smul_apply, Function.comp_apply, h, map_smul, hAB]
    rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearEquiv.adjointEquiv_apply]
  have hBA : ContinuousLinearMap.adjoint (B.symm : E →L[ℝ] E) = A := by
    have : (B.symm : E →L[ℝ] E) = ContinuousLinearMap.adjoint (A : E →L[ℝ] E) := by
      ext ζ
      simp [B]
    rw [this, ContinuousLinearMap.adjoint_adjoint]
  have hdet : (A.toLinearEquiv : E →ₗ[ℝ] E).det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  rw [hfun, ← Complex.coe_smul, Real.fourierInv_const_smul, Pi.smul_apply, Complex.coe_smul,
    B.fourierInv_comp, hBA, hdetB]
  simp only [ContinuousLinearEquiv.symm_apply_apply, h, smul_smul, abs_inv, inv_inv]
  rw [inv_mul_cancel₀ (abs_ne_zero.2 hdet), one_smul, ContinuousLinearEquiv.coe_coe]

/-- **Linear change of coordinates for a symbol.** For a symbol `a` of order `m` and a linear
automorphism `A` of `ℝⁿ`, the operator `u ↦ Op(a) (u ∘ A) ∘ A⁻¹`, which is `Op(a)` written in the
coordinates `y = A x`, is the quantization of the symbol `(y, η) ↦ a(A⁻¹ y, Aᵀ η)` of order `m`. -/
theorem Symbol.quantizeSchwartzValue_compProdMap_symm_adjointEquiv {n : ℕ} (a : Symbol n V W m)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue
        (Symbol.compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
          a).coefficient u (A x) =
      quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x :=
  (quantizeSchwartzValue_compCLMOfContinuousLinearEquiv a.coefficient A u x).symm

/-- **Linear change of coordinates for the operator on Schwartz space.** For a symbol `a` with
uniform estimates, `u ↦ Op(a) (u ∘ A) ∘ A⁻¹` is the quantization of the symbol
`(y, η) ↦ a(A⁻¹ y, Aᵀ η)`. -/
theorem Symbol.quantizeUniformCLM_compProdMap_symm_adjointEquiv {n : ℕ} {a : Symbol n V W m}
    (ha : a.IsUniform) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    quantizeUniformCLM
        (Symbol.compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv a)
        (ha.compProdMap _ _) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm ∘L quantizeUniformCLM a ha ∘L
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A := by
  ext u x
  simpa using quantizeSchwartzValue_compProdMap_symm_adjointEquiv a A u (A.symm x)

/-- **Invariant operators have invariant symbols.** The quantization of `a` commutes with the
change of coordinates `u ↦ u ∘ A` exactly when `a` is invariant under the change of variables
`(y, η) ↦ (A⁻¹ y, Aᵀ η)`. -/
theorem Symbol.compProdMap_symm_adjointEquiv_eq_self_iff [CompleteSpace V] [CompleteSpace W]
    {n : ℕ} {a : Symbol n V W m} (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    Symbol.compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv a = a ↔
      ∀ (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n),
        quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
          quantizeSchwartzValue a.coefficient u (A x) := by
  refine ⟨fun h u x => ?_, fun h => Symbol.quantizeSchwartzValue_injective
    (funext fun u => funext fun y => ?_)⟩
  · rw [← quantizeSchwartzValue_compProdMap_symm_adjointEquiv, h]
  · have := (quantizeSchwartzValue_compProdMap_symm_adjointEquiv a A u (A.symm y)).trans
      (h u (A.symm y))
    rwa [A.apply_symm_apply] at this

end Quantization

end TauCeti
