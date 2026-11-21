/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Averaging.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Averaging classical symbols over a compact group

Let a compact group `G` act linearly on `ℝⁿ` by `ρ`, and on the coefficient spaces `V` and `W` by
`σ` and `τ`, continuously in the operator norm. A symbol is transported along `g ∈ G` by

`(g • a)(x, ξ) = τ(g) ∘ a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) ∘ σ(g)⁻¹`

(`TauCeti.Symbol.transport`), and averaged by `∫ g • a dμ(g)` (`TauCeti.Symbol.average`). This
file shows that averaging preserves the classical symbols, termwise.

* `TauCeti.HomogeneousSymbol.transport` transports a homogeneous symbol of degree `m` on a real
  Hilbert space in the same way; the result is homogeneous of degree `m`, since `ρ(g)ᵀ` is
  linear. `TauCeti.ClassicalSymbol.transport` transports a classical symbol of order `m`: its
  full symbol is `TauCeti.Symbol.transport` of the full symbol and its homogeneous terms are the
  transported terms, so its principal symbol is the transported principal symbol
  (`TauCeti.ClassicalSymbol.principal_transport`).
* `TauCeti.HomogeneousSymbol.average` averages a homogeneous symbol. Its jets are jointly
  continuous in `g` away from the zero frequency
  (`TauCeti.HomogeneousSymbol.continuousOn_iteratedFDeriv_transport`), so it is an instance of
  the compact parameter integral `TauCeti.HomogeneousSymbol.integral`. For a left-invariant
  measure it is invariant (`TauCeti.HomogeneousSymbol.transport_average`), and for a probability
  measure it fixes invariant homogeneous symbols (`TauCeti.HomogeneousSymbol.average_eq_self`).
* `TauCeti.ClassicalSymbol.average`: **the average of a classical symbol of order `m` is
  classical of order `m`**. Its full symbol is the average of the full symbol
  (`TauCeti.ClassicalSymbol.toSymbol_average`), so its quantization is the average of the
  conjugated operators and is equivariant; its homogeneous terms are the averages of the
  homogeneous terms (`TauCeti.ClassicalSymbol.term_average`), and its principal symbol is the
  average of the principal symbol (`TauCeti.ClassicalSymbol.principal_average`). In particular,
  for a probability measure, **averaging keeps an invariant principal symbol**
  (`TauCeti.ClassicalSymbol.principal_average_of_forall_transport_eq`), while the lower-order
  terms may change. The average is invariant for a left-invariant measure
  (`TauCeti.ClassicalSymbol.transport_average`) and fixes invariant classical symbols for a
  probability measure (`TauCeti.ClassicalSymbol.average_eq_self`).

The point is the uniform control of the remainders. For a cutoff `χ`, the remainder of `g • a`
after `N` terms is the transport of the remainder of `a`, which satisfies the estimates of order
`m - N` uniformly in `g` (`TauCeti.Symbol.exists_bound_transport`), plus the terms
`(χ(ρ(g)ᵀ ξ) - χ(ξ)) (g • a_{m-j})(x, ξ)` for `j < N`, which come from transporting the cutoff.
On the compact group these vanish for `‖ξ‖` larger than a fixed radius, and their jets are
jointly continuous, so they satisfy the estimates of every order uniformly in `g`
(`TauCeti.Symbol.exists_bound_of_continuous_jets_of_eq_zero`). Thus the family of transported
classical symbols satisfies the hypotheses of the compact parameter integral
`TauCeti.ClassicalSymbol.integral`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  (5.5)–(5.6), pp. 516–517: averaging pseudodifferential operators over a compact group, which
  preserves the principal symbol of an invariant operator.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III, proof of Theorem 9.7,
  p. 214: compact-group averaging of operators.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace TauCeti

/-! ### Transport and average of homogeneous symbols -/

namespace HomogeneousSymbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Transport

/-- **Transport of a homogeneous symbol along a linear symmetry.** For a linear automorphism `A`
of `E` and automorphisms `e` of `V` and `f` of `W`, the homogeneous symbol
`(x, ξ) ↦ f ∘ a(A⁻¹ x, Aᵀ ξ) ∘ e⁻¹` of degree `m`. -/
def transport (A : E ≃L[ℝ] E) (e : V ≃L[ℂ] V) (f : W ≃L[ℂ] W)
    (a : HomogeneousSymbol E E V W m) : HomogeneousSymbol E E V W m :=
  (a.compProdMap (A.symm : E →L[ℝ] E) A.adjointEquiv).map
    ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ)

@[simp]
theorem coefficient_transport (A : E ≃L[ℝ] E) (e : V ≃L[ℂ] V) (f : W ≃L[ℂ] W)
    (a : HomogeneousSymbol E E V W m) (p : E × E) :
    (transport A e f a).coefficient p =
      (f : W →L[ℂ] W) ∘L a.coefficient (A.symm p.1, A.adjointEquiv p.2) ∘L
        (e.symm : V →L[ℂ] V) :=
  ContinuousLinearMap.ext fun v ↦ by simp [transport]

@[simp]
theorem transport_add (A : E ≃L[ℝ] E) (e : V ≃L[ℂ] V) (f : W ≃L[ℂ] W)
    (a b : HomogeneousSymbol E E V W m) :
    transport A e f (a + b) = transport A e f a + transport A e f b :=
  HomogeneousSymbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp)

@[simp]
theorem transport_smul (A : E ≃L[ℝ] E) (e : V ≃L[ℂ] V) (f : W ≃L[ℂ] W) (c : ℂ)
    (a : HomogeneousSymbol E E V W m) : transport A e f (c • a) = c • transport A e f a :=
  HomogeneousSymbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp)

/-- Transport along the identity leaves a homogeneous symbol unchanged. -/
@[simp]
theorem transport_one (a : HomogeneousSymbol E E V W m) : transport 1 1 1 a = a := by
  refine HomogeneousSymbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ ?_)
  simp [ContinuousLinearEquiv.one_eq_refl, ContinuousLinearEquiv.adjointEquiv_apply,
    ContinuousLinearMap.adjoint_id]

/-- Transport is compatible with composition of the symmetries: transporting along
`(B, e', f')` and then along `(A, e, f)` is transporting along `(A B, e e', f f')`. -/
theorem transport_transport (A B : E ≃L[ℝ] E) (e e' : V ≃L[ℂ] V) (f f' : W ≃L[ℂ] W)
    (a : HomogeneousSymbol E E V W m) :
    transport A e f (transport B e' f' a) = transport (A * B) (e * e') (f * f') a := by
  refine HomogeneousSymbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ ?_)
  simp [ContinuousLinearEquiv.mul_eq_trans, ContinuousLinearEquiv.adjointEquiv_apply,
    ← ContinuousLinearEquiv.comp_coe, ContinuousLinearMap.adjoint_comp]

end Transport

section Average

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  {ρ : G →* (E ≃L[ℝ] E)} {σ : G →* (V ≃L[ℂ] V)} {τ : G →* (W ≃L[ℂ] W)}
  (hρ : Continuous fun g ↦ (ρ g : E →L[ℝ] E)) (hσ : Continuous fun g ↦ (σ g : V →L[ℂ] V))
  (hτ : Continuous fun g ↦ (τ g : W →L[ℂ] W))

omit [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- The jets of the transported homogeneous symbols `g • a` are jointly continuous in `g` and the
position-frequency variables away from the zero frequency. -/
theorem continuousOn_iteratedFDeriv_transport (a : HomogeneousSymbol E E V W m) (k : ℕ) :
    ContinuousOn (fun q : G × (E × E) ↦
        iteratedFDeriv ℝ k (transport (ρ q.1) (σ q.1) (τ q.1) a).coefficient q.2)
      (univ ×ˢ {p | p.2 ≠ 0}) := by
  -- All transported coefficients are slices of the function `L ∘ a(P x, Q ξ) ∘ R` of the
  -- parameters `(P, Q, L, R)` and of `(x, ξ)`, which is smooth where `Q` is invertible and
  -- `ξ ≠ 0`.
  let U : (((E →L[ℝ] E) × (E →L[ℝ] E)) × ((W →L[ℂ] W) × (V →L[ℂ] V))) × (E × E) →
      V →L[ℂ] W :=
    fun z ↦ z.1.2.1 ∘L a.coefficient (z.1.1.1 z.2.1, z.1.1.2 z.2.2) ∘L z.1.2.2
  let s : Set (((E →L[ℝ] E) × (E →L[ℝ] E)) × ((W →L[ℂ] W) × (V →L[ℂ] V))) :=
    {z | IsUnit z.1.2}
  let t : Set (E × E) := {p | p.2 ≠ 0}
  have hs : IsOpen s := Units.isOpen.preimage continuous_fst.snd
  have ht : IsOpen t := isOpen_ne_fun continuous_snd continuous_const
  have ha : ContDiffOn ℝ ∞ (fun z : (((E →L[ℝ] E) × (E →L[ℝ] E)) ×
      ((W →L[ℂ] W) × (V →L[ℂ] V))) × (E × E) ↦ a.coefficient (z.1.1.1 z.2.1, z.1.1.2 z.2.2))
      (s ×ˢ t) := by
    refine a.contDiffOn_coefficient.comp (((contDiff_fst.fst.fst.clm_apply contDiff_snd.fst).prodMk
      (contDiff_fst.fst.snd.clm_apply contDiff_snd.snd)).contDiffOn) fun z hz hQ ↦ hz.2 ?_
    -- An invertible `Q` has trivial kernel.
    obtain ⟨u, hu⟩ := hz.1
    have h := congrArg (↑u⁻¹ : E →L[ℝ] E) hQ
    rwa [← hu, ← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self, map_zero] at h
  -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map, is smooth.
  have hU : ContDiffOn ℝ ∞ U (s ×ˢ t) :=
    (((ContinuousLinearMap.compL ℂ V W W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff
      (n := ∞)).comp_contDiffOn (contDiff_fst.snd.fst.contDiffOn.prodMk
      ((((ContinuousLinearMap.compL ℂ V V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap
        |>.contDiff (n := ∞)).comp_contDiffOn (ha.prodMk contDiff_fst.snd.snd.contDiffOn)))
  refine ((hU.continuousOn_iteratedFDerivWithin_prod_right (hs.prod ht).uniqueDiffOn k
    (by simp)).comp (((continuous_transportParams hρ hσ hτ).comp continuous_fst).prodMk
      continuous_snd).continuousOn
      fun q (hq : q ∈ univ ×ˢ t) ↦ ⟨⟨(ρ q.1).adjointEquiv.toUnit, rfl⟩, hq.2⟩).congr
      fun q hq ↦ ?_
  have hfun : (fun y ↦ U (((((ρ q.1).symm : E →L[ℝ] E), ((ρ q.1).adjointEquiv : E →L[ℝ] E)),
      ((τ q.1 : W →L[ℂ] W), ((σ q.1).symm : V →L[ℂ] V))), y)) =
      (transport (ρ q.1) (σ q.1) (τ q.1) a).coefficient :=
    funext fun y ↦ (coefficient_transport _ _ _ _ y).symm
  simp only [Function.comp_apply, hfun, iteratedFDerivWithin_of_isOpen k ht hq.2]

/-- **The average of a homogeneous symbol over a compact group.** For a compact group `G` acting
continuously by `ρ` on `E` and by `σ`, `τ` on `V`, `W`, and a finite measure `μ` on `G`, the
homogeneous symbol `∫ g • a dμ(g)` of degree `m`, where
`(g • a)(x, ξ) = τ(g) ∘ a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) ∘ σ(g)⁻¹` (`TauCeti.HomogeneousSymbol.transport`). -/
def average (a : HomogeneousSymbol E E V W m) : HomogeneousSymbol E E V W m :=
  integral μ (fun g ↦ transport (ρ g) (σ g) (τ g) a)
    (continuousOn_iteratedFDeriv_transport hρ hσ hτ a)

/-- The coefficient of the average is the average of the transported coefficients. -/
@[simp]
theorem coefficient_average (a : HomogeneousSymbol E E V W m) (p : E × E) :
    (average μ hρ hσ hτ a).coefficient p =
      ∫ g, (τ g : W →L[ℂ] W) ∘L a.coefficient ((ρ g).symm p.1, (ρ g).adjointEquiv p.2) ∘L
        ((σ g).symm : V →L[ℂ] V) ∂μ := by
  simp only [average, coefficient_integral, coefficient_transport]

/-- Averaging is additive. -/
theorem average_add (a b : HomogeneousSymbol E E V W m) :
    average μ hρ hσ hτ (a + b) = average μ hρ hσ hτ a + average μ hρ hσ hτ b := by
  simp only [average, transport_add]
  exact HomogeneousSymbol.integral_add μ _ (continuousOn_iteratedFDeriv_transport hρ hσ hτ a) _
    (continuousOn_iteratedFDeriv_transport hρ hσ hτ b)

/-- Averaging commutes with multiplication by complex scalars. -/
theorem average_smul (c : ℂ) (a : HomogeneousSymbol E E V W m) :
    average μ hρ hσ hτ (c • a) = c • average μ hρ hσ hτ a := by
  simp only [average, transport_smul]
  exact HomogeneousSymbol.integral_smul μ _ (continuousOn_iteratedFDeriv_transport hρ hσ hτ a) c

/-- **The average is invariant.** For a left-invariant measure, transporting the average of a
homogeneous symbol along the action of any `h ∈ G` gives the average back. -/
theorem transport_average [MeasurableMul G] [μ.IsMulLeftInvariant]
    (a : HomogeneousSymbol E E V W m) (h : G) :
    transport (ρ h) (σ h) (τ h) (average μ hρ hσ hτ a) = average μ hρ hσ hτ a :=
  HomogeneousSymbol.ext (funext fun p ↦ by
    simpa only [coefficient_transport, coefficient_average] using
      comp_integral_transport_comp μ a.coefficient h p)

/-- **Averaging fixes invariant homogeneous symbols.** For a probability measure, a homogeneous
symbol invariant under the action of every `g ∈ G` is its own average. -/
theorem average_eq_self [CompleteSpace (V →L[ℂ] W)] [IsProbabilityMeasure μ]
    {a : HomogeneousSymbol E E V W m} (ha : ∀ g, transport (ρ g) (σ g) (τ g) a = a) :
    average μ hρ hσ hτ a = a := by
  simp only [average, ha]
  exact integral_const_of_probability μ a

/-- **Averaging is idempotent** for a left-invariant probability measure. -/
@[simp]
theorem average_average [MeasurableMul G] [μ.IsMulLeftInvariant] [CompleteSpace (V →L[ℂ] W)]
    [IsProbabilityMeasure μ] (a : HomogeneousSymbol E E V W m) :
    average μ hρ hσ hτ (average μ hρ hσ hτ a) = average μ hρ hσ hτ a :=
  average_eq_self μ hρ hσ hτ (transport_average μ hρ hσ hτ a)

end Average

end HomogeneousSymbol

/-! ### Transport and average of classical symbols -/

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Transport

/-- **Transport of a classical symbol along a linear symmetry.** For a linear automorphism `A` of
`ℝⁿ` and automorphisms `e` of `V` and `f` of `W`, the classical symbol
`(x, ξ) ↦ f ∘ a(A⁻¹ x, Aᵀ ξ) ∘ e⁻¹` of order `m`, whose homogeneous terms are the transported
terms of `a`. Its quantization is `Op(a)` conjugated by the actions of `(A, e, f)`
(`TauCeti.Symbol.quantizeSchwartzValue_transport`). -/
def transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V) (f : W ≃L[ℂ] W)
    (a : ClassicalSymbol n V W m) : ClassicalSymbol n V W m where
  toSymbol := Symbol.transport A e f a.toSymbol
  term j := (a.term j).transport A e f
  exists_remainder' := by
    -- Transport is a linear change of variables, whose remainders exist for some cutoff, followed
    -- by conjugation of the coefficients, which commutes with the expansion.
    obtain ⟨χ, h⟩ := (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      A.adjointEquiv a).exists_remainder'
    refine ⟨χ, fun N ↦ ?_⟩
    obtain ⟨r, hr⟩ := h N
    refine ⟨r.map ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ), fun p ↦ ?_⟩
    simp only [Symbol.coefficient_map, hr, map_sub, map_sum, map_smul,
      HomogeneousSymbol.transport, toSymbol_compProdMap, term_compProdMap,
      HomogeneousSymbol.coefficient_map]
    congr 1
    ext v
    simp

@[simp]
theorem toSymbol_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V)
    (f : W ≃L[ℂ] W) (a : ClassicalSymbol n V W m) :
    (transport A e f a).toSymbol = Symbol.transport A e f a.toSymbol :=
  (rfl)

@[simp]
theorem term_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V)
    (f : W ≃L[ℂ] W) (a : ClassicalSymbol n V W m) (j : ℕ) :
    (transport A e f a).term j = (a.term j).transport A e f :=
  (rfl)

/-- **The principal symbol commutes with transport.** -/
@[simp]
theorem principal_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V)
    (f : W ≃L[ℂ] W) (a : ClassicalSymbol n V W m) :
    (transport A e f a).principal = a.principal.transport A e f :=
  HomogeneousSymbol.ext (funext fun p ↦ by simp)

@[simp]
theorem transport_add (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V)
    (f : W ≃L[ℂ] W) (a b : ClassicalSymbol n V W m) :
    transport A e f (a + b) = transport A e f a + transport A e f b :=
  ext (by simp)

@[simp]
theorem transport_smul (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V)
    (f : W ≃L[ℂ] W) (c : ℂ) (a : ClassicalSymbol n V W m) :
    transport A e f (c • a) = c • transport A e f a :=
  ext (by simp)

/-- Transport along the identity leaves a classical symbol unchanged. -/
@[simp]
theorem transport_one (a : ClassicalSymbol n V W m) : transport 1 1 1 a = a :=
  ext (Symbol.transport_one a.toSymbol)

/-- Transport is compatible with composition of the symmetries. -/
theorem transport_transport (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e e' : V ≃L[ℂ] V)
    (f f' : W ≃L[ℂ] W) (a : ClassicalSymbol n V W m) :
    transport A e f (transport B e' f' a) = transport (A * B) (e * e') (f * f') a :=
  ext (Symbol.transport_transport A B e e' f f' a.toSymbol)

end Transport

section Average

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  {ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)} {σ : G →* (V ≃L[ℂ] V)}
  {τ : G →* (W ≃L[ℂ] W)}
  (hρ : Continuous fun g ↦ (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n))
  (hσ : Continuous fun g ↦ (σ g : V →L[ℂ] V)) (hτ : Continuous fun g ↦ (τ g : W →L[ℂ] W))

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- **Transporting the cutoff.** The transported cut-off term `χ(ρ(g)ᵀ ξ) (g • h)(x, ξ)` and the
cut-off transported term `χ(ξ) (g • h)(x, ξ)` of a homogeneous symbol `h` differ by symbols that
satisfy the estimates of every order `m'` on each compact set of positions, with constants
independent of `g`. -/
private theorem exists_bound_transport_cutoffSymbol_sub {m' : ℝ}
    (h : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g x, x ∈ K → ∀ ξ,
      ‖mixedDeriv α β (Symbol.transport (ρ g) (σ g) (τ g) (HomogeneousSymbol.cutoffSymbol χ h) -
        HomogeneousSymbol.cutoffSymbol χ (h.transport (ρ g) (σ g) (τ g))).coefficient x ξ‖ ≤
          C * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  -- On the compact group `‖ρ(g)‖ ≤ c` uniformly, so `‖ξ‖ ≤ c ‖ρ(g)ᵀ ξ‖`.
  obtain ⟨c₀, hc₀⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  set c := max 1 c₀
  have hc : 1 ≤ c := le_max_left _ _
  have hinv (g : G) (ξ : CoordinateSpace n) : ‖ξ‖ ≤ c * ‖(ρ g).adjointEquiv ξ‖ :=
    ((ρ g).norm_le_norm_symm_mul_norm_adjointEquiv ξ).trans (by
      gcongr
      simpa only [map_inv, ContinuousLinearEquiv.inv_eq_symm] using
        (hc₀ g⁻¹ (mem_univ _)).trans (le_max_right _ _))
  -- Both cutoffs are `1` once `‖ξ‖ > 2c`, so the difference vanishes there.
  refine Symbol.exists_bound_of_continuous_jets_of_eq_zero (fun _ ↦ Symbol.contDiff_coefficient _)
    (fun k ↦ ?_) (fun _ _ ↦ ⟨2 * c, fun g x _ ξ hξ ↦ ?_⟩) m' hK α β
  · have hk : ((k : ℕ∞) : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
    refine ((Symbol.continuous_iteratedFDeriv_transport hρ hσ hτ
      (HomogeneousSymbol.cutoffSymbol χ h) k).sub
      (HomogeneousSymbol.continuous_iteratedFDeriv_smul_coefficient
        (fun g ↦ h.transport (ρ g) (σ g) (τ g))
        (HomogeneousSymbol.continuousOn_iteratedFDeriv_transport hρ hσ hτ h) χ k)).congr
      fun q ↦ ?_
    rw [Symbol.coefficient_sub, iteratedFDeriv_sub_apply
      ((Symbol.contDiff_coefficient _).contDiffAt.of_le hk)
      ((Symbol.contDiff_coefficient _).contDiffAt.of_le hk), Pi.sub_apply,
      funext (HomogeneousSymbol.coefficient_cutoffSymbol χ _)]
  · have h2 := χ.apply_eq_one_of_two_le_norm (show 2 ≤ ‖(ρ g).adjointEquiv ξ‖ by
      nlinarith [hinv g ξ])
    rw [ContinuousLinearEquiv.adjointEquiv_apply] at h2
    simp [h2, χ.apply_eq_one_of_two_le_norm (show 2 ≤ ‖ξ‖ by nlinarith)]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- The remainders after `N` terms of the transported classical symbols `g • a`, for one cutoff,
satisfy the estimates of order `m - N` on each compact set of positions with constants independent
of `g`. -/
private theorem exists_bound_remainder_transport (a : ClassicalSymbol n V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g x, x ∈ K → ∀ ξ,
      ‖mixedDeriv α β ((transport (ρ g) (σ g) (τ g) a).remainder χ N).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  -- The remainder of `g • a` is the transported remainder of `a`, plus the differences `D j g`
  -- between the transported cut-off terms and the cut-off transported terms.
  let D (j : ℕ) (g : G) : Symbol n V W (m - j) :=
    Symbol.transport (ρ g) (σ g) (τ g) (HomogeneousSymbol.cutoffSymbol χ (a.term j)) -
      HomogeneousSymbol.cutoffSymbol χ ((a.term j).transport (ρ g) (σ g) (τ g))
  have hcoef (g : G) : ((transport (ρ g) (σ g) (τ g) a).remainder χ N).coefficient =
      (Symbol.transport (ρ g) (σ g) (τ g) (a.remainder χ N)).coefficient +
        ∑ j ∈ Finset.range N, (D j g).coefficient := by
    funext p
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp [D, coefficient_remainder, Finset.sum_apply, map_sum, Finset.sum_sub_distrib]
  choose C hC0 hC using fun j ↦ exists_bound_transport_cutoffSymbol_sub hρ hσ hτ (m' := m - N)
    (a.term j) χ hK α β
  obtain ⟨B, hB0, hB⟩ := Symbol.exists_bound_transport hρ hσ hτ (a.remainder χ N) K hK α β
  refine ⟨B + ∑ j ∈ Finset.range N, C j,
    add_nonneg hB0 (Finset.sum_nonneg fun j _ ↦ hC0 j), fun g x hx ξ ↦ ?_⟩
  have hsmooth (j : ℕ) : ContDiff ℝ ∞ (D j g).coefficient := (D j g).contDiff_coefficient
  rw [hcoef, mixedDeriv_add (Symbol.contDiff_coefficient _)
    (by rw [Finset.sum_fn]; exact ContDiff.sum fun j _ ↦ hsmooth j),
    mixedDeriv_sum fun j _ ↦ hsmooth j, add_mul, Finset.sum_mul]
  exact (norm_add_le _ _).trans (add_le_add (hB g x hx ξ)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hC j g x hx ξ)))

/-- **The average of a classical symbol over a compact group.** For a compact group `G` acting
continuously by `ρ` on `ℝⁿ` and by `σ`, `τ` on `V`, `W`, and a finite measure `μ` on `G`, the
average `∫ g • a dμ(g)` of a classical symbol `a` of order `m` is classical of order `m`, with
full symbol the average `TauCeti.Symbol.average` of the full symbol
(`TauCeti.ClassicalSymbol.toSymbol_average`) and homogeneous terms the averages of the homogeneous
terms (`TauCeti.ClassicalSymbol.term_average`). -/
def average (a : ClassicalSymbol n V W m) : ClassicalSymbol n V W m :=
  integral μ (fun g ↦ transport (ρ g) (σ g) (τ g) a)
    (fun k ↦ by
      simpa only [toSymbol_transport] using
        Symbol.continuous_iteratedFDeriv_transport hρ hσ hτ a.toSymbol k)
    (fun j k ↦ by
      simpa only [term_transport] using
        HomogeneousSymbol.continuousOn_iteratedFDeriv_transport hρ hσ hτ (a.term j) k)
    ⟨default, fun N K α β ↦ by
      obtain ⟨C, hC0, hC⟩ := exists_bound_remainder_transport hρ hσ hτ a default N K.isCompact α β
      exact ⟨C, by
        rintro _ ⟨g, rfl⟩
        exact Symbol.seminorm_le_bound K α β _ hC0 fun x hx ξ ↦ hC g x hx ξ⟩⟩

/-- The full symbol of the average of a classical symbol is the average of its full symbol. -/
@[simp]
theorem toSymbol_average (a : ClassicalSymbol n V W m) :
    (average μ hρ hσ hτ a).toSymbol = Symbol.average μ hρ hσ hτ a.toSymbol :=
  Symbol.ext (funext fun p ↦ by
    rw [average, coefficient_toSymbol_integral, Symbol.coefficient_average]
    simp)

/-- The homogeneous terms of the average of a classical symbol are the averages of its homogeneous
terms. -/
@[simp]
theorem term_average (a : ClassicalSymbol n V W m) (j : ℕ) :
    (average μ hρ hσ hτ a).term j = HomogeneousSymbol.average μ hρ hσ hτ (a.term j) :=
  HomogeneousSymbol.ext (funext fun p ↦ by
    rw [average, term_integral, HomogeneousSymbol.coefficient_integral,
      HomogeneousSymbol.coefficient_average]
    simp)

/-- **The principal symbol of the average is the average of the principal symbol.** -/
@[simp]
theorem principal_average (a : ClassicalSymbol n V W m) :
    (average μ hρ hσ hτ a).principal = HomogeneousSymbol.average μ hρ hσ hτ a.principal :=
  HomogeneousSymbol.ext (funext fun p ↦ by simp)

/-- Averaging is additive. -/
theorem average_add (a b : ClassicalSymbol n V W m) :
    average μ hρ hσ hτ (a + b) = average μ hρ hσ hτ a + average μ hρ hσ hτ b :=
  ext (by simp [Symbol.average_add])

/-- Averaging commutes with multiplication by complex scalars. -/
theorem average_smul (c : ℂ) (a : ClassicalSymbol n V W m) :
    average μ hρ hσ hτ (c • a) = c • average μ hρ hσ hτ a :=
  ext (by simp [Symbol.average_smul])

/-- **The average is invariant.** For a left-invariant measure, transporting the average along
the action of any `h ∈ G` gives the average back. -/
theorem transport_average [MeasurableMul G] [μ.IsMulLeftInvariant] (a : ClassicalSymbol n V W m)
    (h : G) : transport (ρ h) (σ h) (τ h) (average μ hρ hσ hτ a) = average μ hρ hσ hτ a :=
  ext (by simp [Symbol.transport_average])

/-- **Averaging fixes invariant classical symbols.** For a probability measure, a classical symbol
invariant under the action of every `g ∈ G` is its own average. -/
theorem average_eq_self [CompleteSpace (V →L[ℂ] W)] [IsProbabilityMeasure μ]
    {a : ClassicalSymbol n V W m} (ha : ∀ g, transport (ρ g) (σ g) (τ g) a = a) :
    average μ hρ hσ hτ a = a :=
  ext (by
    rw [toSymbol_average]
    exact Symbol.average_eq_self μ hρ hσ hτ fun g ↦ by rw [← toSymbol_transport, ha g])

/-- **Averaging is idempotent** for a left-invariant probability measure. -/
@[simp]
theorem average_average [MeasurableMul G] [μ.IsMulLeftInvariant] [CompleteSpace (V →L[ℂ] W)]
    [IsProbabilityMeasure μ] (a : ClassicalSymbol n V W m) :
    average μ hρ hσ hτ (average μ hρ hσ hτ a) = average μ hρ hσ hτ a :=
  average_eq_self μ hρ hσ hτ (transport_average μ hρ hσ hτ a)

/-- **Averaging keeps an invariant principal symbol.** For a probability measure, if the
principal symbol of `a` is invariant under the action of every `g ∈ G`, the average of `a` has
the same principal symbol; only the lower-order terms may change. -/
theorem principal_average_of_forall_transport_eq [CompleteSpace (V →L[ℂ] W)]
    [IsProbabilityMeasure μ] {a : ClassicalSymbol n V W m}
    (ha : ∀ g, a.principal.transport (ρ g) (σ g) (τ g) = a.principal) :
    (average μ hρ hσ hτ a).principal = a.principal := by
  rw [principal_average, HomogeneousSymbol.average_eq_self μ hρ hσ hτ ha]

end Average

end ClassicalSymbol

end TauCeti
