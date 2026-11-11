/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Linear changes of variables of symbols and quantizations

Under a linear change of coordinates `y = A x` of `ℝⁿ`, a pseudodifferential operator is again a
pseudodifferential operator, and its full symbol transforms exactly as a function on the
cotangent bundle: positions by `A⁻¹` and frequencies, which are covectors, by the transpose `Aᵀ`.
In the left (Kohn–Nirenberg) quantization this is the identity

`Op(a) (u ∘ A) = Op(b) u ∘ A`, with `b(y, η) = a(A⁻¹ y, Aᵀ η)`

(`TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`). For nonlinear changes of
coordinates the transformed symbol is only determined by an asymptotic expansion whose leading term
is given by the same rule; the linear case has no lower order corrections.

The transformed symbol is a change of variables `(x, ξ) ↦ (P x, Q ξ)` of the position and the
frequency, for a continuous linear map `P` and a linear automorphism `Q`. This file shows that it
preserves the symbol classes and the structures defined on them:

* `TauCeti.Symbol.compProdMap P Q`: the symbol `(x, ξ) ↦ a(P x, Q ξ)`, of the same order `m`, as a
  linear map of symbol classes. It commutes with the inclusions of the classes and the pointwise
  composition, composes as `compProdMap P Q ∘ compProdMap P' Q' = compProdMap (P' ∘ P) (Q' ∘ Q)`,
  and preserves uniform estimates, smoothing symbols, and, for invertible `P`, compact spatial
  support.
* `TauCeti.ClassicalSymbol.compProdMap P Q`: a classical symbol stays classical, with the
  transformed homogeneous terms `a_{m-j}(P x, Q ξ)`, so its principal symbol transforms by the same
  rule (`TauCeti.ClassicalSymbol.principal_compProdMap`) and ellipticity is preserved
  (`TauCeti.ClassicalSymbol.IsElliptic.compProdMap`). The substitution turns the cutoff `χ(ξ)` of
  the expansion into `χ(Q ξ)`, which is not a frequency cutoff in general, but the two cut-off terms
  differ by a smoothing symbol
  (`TauCeti.HomogeneousSymbol.isSmoothing_compProdMap_cutoffSymbol_sub_cutoffSymbol`).
* `TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv`: the change of coordinates of the
  quantization, for an arbitrary coefficient, and
  `TauCeti.Symbol.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv` in terms of
  `Symbol.compProdMap`.

The symbol estimates of `a(P x, Q ξ)` follow from those of `a`: a mixed derivative with `|α|`
position and `|β|` frequency derivatives of the composite is a combination of mixed derivatives of
`a` with the same numbers of derivatives (`TauCeti.norm_mixedDeriv_comp_prodMap_le`), and the
weights `⟨Q ξ⟩` and `⟨ξ⟩` are comparable because `Q` is invertible
(`TauCeti.one_add_norm_sq_rpow_le_of_norm_le_mul`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Section 18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, §8.
-/

public section

noncomputable section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff
open MeasureTheory Real FourierTransform Module

namespace TauCeti

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Symbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- Symbol estimates of order `m` on a set `S` of positions transfer to `(x, ξ) ↦ f(P x, Q ξ)` on
the positions `x` with `P x ∈ S`. -/
private theorem exists_bound_comp_prodMap {f : CoordinateSpace n × CoordinateSpace n → G}
    (hf : ContDiff ℝ ∞ f) (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) {S : Set (CoordinateSpace n)}
    (h : ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ ξ,
      ‖mixedDeriv α β f x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, P x ∈ S → ∀ ξ,
      ‖mixedDeriv α β (fun p => f (P p.1, Q p.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  choose B hB0 hB using h
  -- The weights `⟨Q ξ⟩` and `⟨ξ⟩` are comparable, since `‖Q ξ‖ ≤ c₀ ‖ξ‖` and `‖ξ‖ ≤ c₀ ‖Q ξ‖`.
  set c₀ := max (max ‖(Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖
    ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖) 1
  have hc₀ : 1 ≤ c₀ := le_max_right _ _
  set c := c₀ ^ |m - β.length|
  have hc0 : 0 ≤ c := by positivity
  have hc (ξ : CoordinateSpace n) : (1 + ‖Q ξ‖ ^ 2) ^ ((m - β.length) / 2) ≤
      c * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
    refine one_add_norm_sq_rpow_le_of_norm_le_mul hc₀ _ ?_ ?_
    · exact ((Q : CoordinateSpace n →L[ℝ] CoordinateSpace n).le_opNorm ξ).trans
        (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (norm_nonneg _))
    · calc ‖ξ‖ = ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) (Q ξ)‖ := by simp
        _ ≤ ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ * ‖Q ξ‖ :=
          (Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).le_opNorm _
        _ ≤ c₀ * ‖Q ξ‖ := mul_le_mul_of_nonneg_right
          ((le_max_right _ _).trans (le_max_left _ _)) (norm_nonneg _)
  set M := max ‖P‖ ‖(Q : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖
  set D := ∑ t : Fin (α.length + β.length) → Fin n,
    B (List.ofFn fun i => t (Fin.castAdd β.length i)) (List.ofFn fun i => t (Fin.natAdd α.length i))
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => hB0 _ _
  have hM : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  refine ⟨M ^ (α.length + β.length) * (D * c), by positivity, fun x hx ξ => ?_⟩
  refine (norm_mixedDeriv_comp_prodMap_le α β (hf.of_le (by exact_mod_cast le_top)) P Q x
    ξ).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [D, Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  have h := hB (List.ofFn fun i => t (Fin.castAdd β.length i))
    (List.ofFn fun i => t (Fin.natAdd α.length i)) (P x) hx (Q ξ)
  simp only [List.length_ofFn] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hc ξ) (hB0 _ _)

/-- **Linear change of variables of a symbol.** For a continuous linear map `P` of the positions
and a linear automorphism `Q` of the frequencies, `(x, ξ) ↦ a(P x, Q ξ)` is a symbol of the same
order `m`. The invertibility of `Q` keeps the weight `⟨Q ξ⟩` comparable to `⟨ξ⟩`; no condition on
`P` is needed, since the local estimates on a compact set `K` come from those of `a` on `P '' K`. -/
def compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient := fun p => a.coefficient (P p.1, Q p.2)
      contDiff_coefficient :=
        a.contDiff_coefficient.comp ((P.contDiff.comp contDiff_fst).prodMk
          (Q.contDiff.comp contDiff_snd))
      exists_bound := fun K hK α β => by
        obtain ⟨C, hC0, hC⟩ := exists_bound_comp_prodMap a.contDiff_coefficient P Q
          (S := P '' K) (fun α β => a.exists_bound _ (hK.image P.continuous) α β) α β
        exact ⟨C, hC0, fun x hx ξ => hC x ⟨x, hx, rfl⟩ ξ⟩ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coefficient_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (compProdMap P Q a).coefficient p = a.coefficient (P p.1, Q p.2) :=
  (rfl)

/-- Changing variables twice is changing variables by the composite maps. -/
theorem compProdMap_compProdMap (P P' : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q Q' : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m) :
    compProdMap P Q (compProdMap P' Q' a) = compProdMap (P'.comp P) (Q.trans Q') a :=
  Symbol.ext (funext fun _ => by simp)

@[simp]
theorem compProdMap_id_refl (a : Symbol n V W m) :
    compProdMap (ContinuousLinearMap.id ℝ _) (ContinuousLinearEquiv.refl ℝ _) a = a :=
  Symbol.ext (funext fun _ => by simp)

/-- A linear change of variables commutes with the inclusions of the symbol classes. -/
@[simp]
theorem compProdMap_inclusion {m' : ℝ} (h : m ≤ m') (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : Symbol n V W m) :
    compProdMap P Q (inclusion h a) = inclusion h (compProdMap P Q a) :=
  Symbol.ext (funext fun _ => by simp)

/-- A linear change of variables commutes with the pointwise composition of symbols. -/
@[simp]
theorem compProdMap_comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] {m' : ℝ}
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (b : Symbol n W U m') (a : Symbol n V W m) :
    compProdMap P Q (b.comp a) = (compProdMap P Q b).comp (compProdMap P Q a) :=
  Symbol.ext (funext fun _ => by simp [coefficient_comp])

/-- A linear change of variables preserves estimates uniform in the position. -/
theorem IsUniform.compProdMap {a : Symbol n V W m} (ha : a.IsUniform)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (compProdMap P Q a).IsUniform := by
  refine isUniform_iff.2 fun α β => ?_
  obtain ⟨C, hC0, hC⟩ := exists_bound_comp_prodMap a.contDiff_coefficient P Q (S := Set.univ)
    (fun α β => (isUniform_iff.1 ha α β).imp fun _ hC => ⟨hC.1, fun x _ ξ => hC.2 x ξ⟩) α β
  exact ⟨C, hC0, fun x ξ => hC x trivial ξ⟩

/-- An invertible linear change of the positions preserves compact spatial support. -/
theorem HasCompactSpatialSupport.compProdMap {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (P Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n) Q a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  exact hasCompactSpatialSupport_iff.2 ⟨P.symm '' K, hK.image P.symm.continuous,
    fun x hx ξ => hKa _ (fun hPx => hx ⟨P x, hPx, P.symm_apply_apply x⟩) _⟩

/-- A linear change of variables preserves smoothing symbols. -/
theorem IsSmoothing.compProdMap {a : Symbol n V W m} (ha : a.IsSmoothing)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (compProdMap P Q a).IsSmoothing :=
  isSmoothing_iff.2 fun m' => by
    obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
    exact ⟨Symbol.compProdMap P Q b, funext fun p => by simp [hb]⟩

end Symbol

namespace HomogeneousSymbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- Changing variables in a cut-off homogeneous term agrees, up to a smoothing symbol, with cutting
off the transformed term: `χ(Q ξ) a(P x, Q ξ)` and `χ(ξ) a(P x, Q ξ)` coincide at all large
frequencies, where both cutoffs equal `1`. -/
theorem isSmoothing_compProdMap_cutoffSymbol_sub_cutoffSymbol {n : ℕ}
    (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) :
    (Symbol.compProdMap P Q (cutoffSymbol χ a) -
      cutoffSymbol χ ((a.compPosition P P.contDiff).compFrequency Q)).IsSmoothing := by
  set c := max ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ 1
  have hc : 1 ≤ c := le_max_right _ _
  refine Symbol.isSmoothing_of_coefficient_eq_zero (2 * c) fun x ξ hξ => ?_
  have h2 : 2 ≤ ‖ξ‖ := by nlinarith
  have hQ : 2 ≤ ‖Q ξ‖ := by
    have hle : ‖ξ‖ ≤ c * ‖Q ξ‖ :=
      calc ‖ξ‖ = ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) (Q ξ)‖ := by simp
        _ ≤ ‖(Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ * ‖Q ξ‖ :=
          (Q.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).le_opNorm _
        _ ≤ c * ‖Q ξ‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    by_contra h
    nlinarith [not_le.1 h]
  simp [χ.apply_eq_one_of_two_le_norm h2, χ.apply_eq_one_of_two_le_norm hQ]

end HomogeneousSymbol

namespace ClassicalSymbol

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

open HomogeneousSymbol

/-- **Linear change of variables of a classical symbol.** The symbol `(x, ξ) ↦ a(P x, Q ξ)` is
classical, with homogeneous terms `a_{m-j}(P x, Q ξ)`. The cutoff `χ(Q ξ)` that the substitution
produces is replaced by `χ(ξ)` at the cost of smoothing symbols
(`TauCeti.HomogeneousSymbol.isSmoothing_compProdMap_cutoffSymbol_sub_cutoffSymbol`). -/
def compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    ClassicalSymbol n V W m where
  toSymbol := Symbol.compProdMap P Q a.toSymbol
  term j := ((a.term j).compPosition P P.contDiff).compFrequency Q
  exists_remainder' := by
    obtain ⟨χ, -⟩ := a.exists_remainder'
    refine ⟨χ, fun N => ?_⟩
    choose s hs using fun j => Symbol.isSmoothing_iff.1
      (isSmoothing_compProdMap_cutoffSymbol_sub_cutoffSymbol χ (a.term j) P Q) (m - N)
    refine ⟨Symbol.compProdMap P Q (a.remainder χ N) + ∑ j ∈ Finset.range N, s j, fun p => ?_⟩
    simp only [Symbol.coefficient_add, Pi.add_apply, Symbol.coefficient_sum, Finset.sum_apply, hs,
      Symbol.coefficient_compProdMap, coefficient_remainder, Symbol.coefficient_sub, Pi.sub_apply,
      coefficient_cutoffSymbol, Finset.sum_sub_distrib, coefficient_compFrequency,
      coefficient_compPosition]
    abel

@[simp]
theorem toSymbol_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    (a.compProdMap P Q).toSymbol = Symbol.compProdMap P Q a.toSymbol :=
  (rfl)

@[simp]
theorem term_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) (j : ℕ) :
    (a.compProdMap P Q).term j = ((a.term j).compPosition P P.contDiff).compFrequency Q :=
  (rfl)

/-- **The principal symbol transforms as a function of covectors.** Under the linear change of
variables `(x, ξ) ↦ (P x, Q ξ)`, the principal symbol is the transformed principal symbol
`a_m(P x, Q ξ)`. -/
theorem principal_compProdMap (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (a : ClassicalSymbol n V W m) :
    (a.compProdMap P Q).principal = (a.principal.compPosition P P.contDiff).compFrequency Q :=
  HomogeneousSymbol.ext (funext fun p => by simp)

/-- A linear change of variables preserves ellipticity. -/
theorem IsElliptic.compProdMap {a : ClassicalSymbol n V W m} (ha : a.IsElliptic)
    (P : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (Q : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) : (a.compProdMap P Q).IsElliptic := by
  rw [isElliptic_def, principal_compProdMap]
  exact (isElliptic_def.1 ha).compPosition P P.contDiff |>.compFrequency Q

end ClassicalSymbol

section Quantization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Linear change of coordinates of a quantization.** For a linear automorphism `A` of `E`,
quantizing `a` on the pullback `u ∘ A` is pulling back the quantization of the transformed
coefficient `b(y, η) = a(A⁻¹ y, Aᵀ η)` on `u`:

`Op(a) (u ∘ A) (x) = Op(b) u (A x)`.

Positions transform by `A⁻¹` and frequencies, being covectors, by the transpose `Aᵀ`. No growth
or smoothness assumption on `a` is needed: both sides are the same Bochner integral after the
substitution `ζ = Aᵀ ζ'` in the frequency. -/
theorem quantizeSchwartzValue_compCLMOfContinuousLinearEquiv (a : E × E → V →L[ℂ] W)
    (A : E ≃L[ℝ] E) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (fun p => a (A.symm p.1, A.adjointEquiv p.2)) u (A x) := by
  set B := A.adjointEquiv
  have hd : |A.toLinearEquiv.toLinearMap.det| ≠ 0 :=
    abs_ne_zero.2 A.toLinearEquiv.isUnit_det'.ne_zero
  have hdet : B.toLinearEquiv.toLinearMap.det = A.toLinearEquiv.toLinearMap.det := by
    have hB : B.toLinearEquiv.toLinearMap = LinearMap.adjoint A.toLinearEquiv.toLinearMap := by
      ext ζ
      simpa [B] using (congrArg (fun f : E →ₗ[ℝ] E => f ζ)
        (ContinuousLinearMap.adjoint_toLinearMap (A : E →L[ℝ] E))).symm
    rw [hB, LinearMap.det_adjoint, star_trivial]
  set g : E → W := fun ζ => 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 (u ∘ A) ζ)
  have hL : quantizeSchwartzValue a (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      ∫ ζ, g ζ := by
    simp only [quantizeSchwartzValue_def, g, SchwartzMap.fourier_coe,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  have hR : quantizeSchwartzValue (fun p => a (A.symm p.1, B p.2)) u (A x) =
      |A.toLinearEquiv.toLinearMap.det| • ∫ ζ, g (B ζ) := by
    rw [quantizeSchwartzValue_def, ← integral_smul]
    congr 1
    funext ζ
    simp only [g, A.fourier_comp, B, ContinuousLinearEquiv.adjointEquiv_apply,
      ContinuousLinearEquiv.adjoint_symm_adjoint_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, map_smul,
      SchwartzMap.fourier_coe]
    rw [ContinuousLinearMap.map_smul_of_tower, smul_comm |A.toLinearEquiv.toLinearMap.det|,
      smul_smul, mul_inv_cancel₀ hd, one_smul]
  rw [hL, hR, Measure.integral_comp_continuousLinearEquiv volume g B, hdet, smul_smul,
    mul_inv_cancel₀ hd, one_smul]

/-- **Linear change of coordinates of the quantization of a symbol.** For a linear automorphism
`A` of `ℝⁿ`, `Op(a) (u ∘ A) = Op(b) u ∘ A` with the symbol `b(y, η) = a(A⁻¹ y, Aᵀ η)` of the same
order. -/
theorem Symbol.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv {n : ℕ} {m : ℝ}
    (a : Symbol n V W m) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A u) x =
      quantizeSchwartzValue (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
        A.adjointEquiv a).coefficient u (A x) := by
  have h : (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
      a).coefficient = fun p => a.coefficient (A.symm p.1, A.adjointEquiv p.2) :=
    funext (coefficient_compProdMap _ _ a)
  rw [h]
  exact TauCeti.quantizeSchwartzValue_compCLMOfContinuousLinearEquiv _ A u x

end Quantization

end TauCeti
