/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Analysis.Pseudodifferential.Integral
public import TauCeti.Analysis.Pseudodifferential.LinearChange
public import TauCeti.Analysis.Pseudodifferential.Symbol.Map
public import TauCeti.Topology.Algebra.Module.Equiv.AutomorphismGroup
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# Averaging symbols over a compact group

Let a compact group `G` act linearly on `ℝⁿ` by `ρ`, and on the coefficient spaces `V` and `W` by
representations `σ` and `τ`, all continuously in the operator norm. Then `G` acts on functions by
`(g • u)(x) = σ(g) u(ρ(g)⁻¹ x)`, and on symbols by

`(g • a)(x, ξ) = τ(g) ∘ a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) ∘ σ(g)⁻¹`,

so that positions move by `ρ(g)` and frequencies, being covectors, by the inverse transpose. The
quantization intertwines the two actions exactly: `Op(g • a) = g • Op(a) • g⁻¹`
(`TauCeti.Symbol.quantizeSchwartzValue_transport`). This is the linear change of coordinates of
`TauCeti.Symbol.quantizeSchwartzValue_compProdMap_symm_adjointEquiv`, followed by conjugation of
the coefficients. More generally a symbol can be transported along isomorphisms `V ≃ V'`,
`W ≃ W'` of the coefficient spaces (`TauCeti.Symbol.transport`). Transport is functorial
(`TauCeti.Symbol.transport_transport`, `TauCeti.Symbol.transport_mul`), and, as a linear change of
variables followed by a change of coefficients (`TauCeti.Symbol.transport_eq_map_compProdMap`), it
preserves smoothing symbols, uniform estimates and compact spatial support
(`TauCeti.Symbol.IsSmoothing.transport`, `TauCeti.Symbol.IsUniform.transport`,
`TauCeti.Symbol.HasCompactSpatialSupport.transport`).

For a left-invariant finite measure `μ` on `G`, such as the normalized Haar measure
`TauCeti.haarProb G`, the **average** `∫ g • a dμ(g)` of a symbol `a` of order `m` is again a
symbol of order `m` (`TauCeti.Symbol.average`). The symbol estimates of `g • a` hold with
constants independent of `g`, since `ρ`, `σ` and `τ` are bounded on the compact group and
positions in a compact set `K` are sent into the compact set `ρ(G)⁻¹ K`; so the average is an
instance of the compact parameter integral `TauCeti.Symbol.integral`. Its main properties are:

* `TauCeti.Symbol.transport_average`: the average is invariant, `h • avg(a) = avg(a)`.
* `TauCeti.Symbol.quantizeSchwartzValue_average_transport`: hence the averaged operator is
  equivariant, `Op(avg a)(h • u) = h • Op(avg a) u`. More generally every invariant symbol
  quantizes to an equivariant operator (`TauCeti.Symbol.quantizeSchwartzValue_of_transport_eq`),
  for the representation `TauCeti.schwartzRep` of `G` on Schwartz functions
  (`TauCeti.Symbol.quantizeSchwartzValue_schwartzRep`).
* `TauCeti.Symbol.quantizeSchwartzValue_average`: the averaged operator is the average of the
  conjugated operators, `Op(avg a) u = ∫ g • Op(a)(g⁻¹ • u) dμ(g)`.
* `TauCeti.Symbol.average_eq_smul_self`: averaging multiplies an invariant symbol by the total
  mass of `μ`. So for a probability measure, averaging fixes invariant symbols
  (`TauCeti.Symbol.average_eq_self`), and these are exactly the symbols it fixes
  (`TauCeti.Symbol.average_eq_self_iff`); in particular it is idempotent
  (`TauCeti.Symbol.average_average`). Trivial actions fix every symbol
  (`TauCeti.Symbol.transport_one`), so for them averaging is the identity.
* Seminorm bounds on `g • a` uniform in `g` pass to the average
  (`TauCeti.Symbol.seminorm_average_le`, `TauCeti.Symbol.seminorm_average_le_of_probability`).
* Averaging is `ℂ`-linear (`TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`) and
  preserves smoothing symbols, estimates uniform in the position and compact spatial support
  (`TauCeti.Symbol.IsSmoothing.average`, `TauCeti.Symbol.IsUniform.average`,
  `TauCeti.Symbol.HasCompactSpatialSupport.average`).

For instance, for the reflection group `{±1}` acting on `ℝ` with trivial actions on the
coefficients, the average of the order-zero symbol `x` is `(x - x)/2 = 0`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  (5.5)–(5.6), pp. 516–517: averaging pseudodifferential operators over a compact group.
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Chapter III, proof of Theorem 9.7,
  p. 214: compact-group averaging of operators.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap

namespace TauCeti

section SchwartzRep

variable {G : Type*} [Group G] {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The representation of `G` on `V`-valued Schwartz functions induced by actions `ρ` on `ℝⁿ` and
`σ` on `V`: `(g • u)(x) = σ(g) u(ρ(g)⁻¹ x)`. This is the action on inputs in
`TauCeti.Symbol.quantizeSchwartzValue_transport`. -/
def schwartzRep (ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)) (σ : G →* (V ≃L[ℂ] V)) :
    G →* (𝓢(CoordinateSpace n, V) →L[ℂ] 𝓢(CoordinateSpace n, V)) where
  toFun g := (SchwartzMap.postcompCLM (σ g : V →L[ℂ] V)).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm)
  map_one' := by
    ext u x
    simp [ContinuousLinearEquiv.one_eq_refl]
  map_mul' g h := by
    ext u x
    simp [ContinuousLinearEquiv.mul_eq_trans]

@[simp]
theorem schwartzRep_apply (ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n))
    (σ : G →* (V ≃L[ℂ] V)) (g : G) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    schwartzRep ρ σ g u x = σ g (u ((ρ g).symm x)) := by
  simp [schwartzRep]

end SchwartzRep

namespace Symbol

variable {n : ℕ} {V W V' W' V'' W'' : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
  [NormedAddCommGroup V''] [NormedSpace ℂ V''] [NormedAddCommGroup W''] [NormedSpace ℂ W'']
  {m : ℝ}

section Transport

/-- **Transport of a symbol along a linear symmetry.** For a linear automorphism `A` of `ℝⁿ` and
isomorphisms `e : V ≃ V'` and `f : W ≃ W'`, the symbol `(x, ξ) ↦ f ∘ a(A⁻¹ x, Aᵀ ξ) ∘ e⁻¹` of
order `m`. Its quantization is `Op(a)` conjugated by `u ↦ e ∘ u ∘ A⁻¹` on inputs and by
`v ↦ f ∘ v ∘ A⁻¹` on outputs (`TauCeti.Symbol.quantizeSchwartzValue_transport`). -/
def transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W')
    (a : Symbol n V W m) : Symbol n V' W' m :=
  (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv a).map
    ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ)

/-- The coefficient of the transported symbol, as the conjugation `T ↦ f ∘ T ∘ e⁻¹` applied to a
linear change of variables of the coefficient. -/
private theorem coefficient_transport_eq_comp (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) :
    (transport A e f a).coefficient =
      ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ) ∘
        (a.coefficient ∘ (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
          (A.adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)) :=
  funext fun ⟨x, ξ⟩ ↦ by simp [transport]

@[simp]
theorem coefficient_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V')
    (f : W ≃L[ℂ] W') (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (transport A e f a).coefficient p =
      (f : W →L[ℂ] W') ∘L a.coefficient (A.symm p.1, A.adjointEquiv p.2) ∘L
        (e.symm : V' →L[ℂ] V) :=
  ContinuousLinearMap.ext fun v ↦ by simp [transport]

@[simp]
theorem transport_zero (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V')
    (f : W ≃L[ℂ] W') : transport A e f (0 : Symbol n V W m) = 0 :=
  Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp)

@[simp]
theorem transport_add (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V')
    (f : W ≃L[ℂ] W') (a b : Symbol n V W m) :
    transport A e f (a + b) = transport A e f a + transport A e f b :=
  Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp)

@[simp]
theorem transport_smul (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V')
    (f : W ≃L[ℂ] W') (c : ℂ) (a : Symbol n V W m) :
    transport A e f (c • a) = c • transport A e f a :=
  Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp)

/-- Transport along the identity leaves a symbol unchanged. -/
@[simp]
theorem transport_one (a : Symbol n V W m) : transport 1 1 1 a = a := by
  refine Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ ?_)
  simp [ContinuousLinearEquiv.one_eq_refl, ContinuousLinearEquiv.adjointEquiv_apply,
    ContinuousLinearMap.adjoint_id]

/-- Transport along the identity symmetries leaves a symbol unchanged. -/
@[simp]
theorem transport_refl (a : Symbol n V W m) :
    transport (.refl ℝ (CoordinateSpace n)) (.refl ℂ V) (.refl ℂ W) a = a := by
  simpa only [ContinuousLinearEquiv.one_eq_refl] using transport_one a

/-- Transport is functorial: transporting along `(B, e₁, f₁)` and then along `(A, e₂, f₂)` is
transporting along the composites. -/
@[simp]
theorem transport_transport (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e₁ : V ≃L[ℂ] V')
    (e₂ : V' ≃L[ℂ] V'') (f₁ : W ≃L[ℂ] W') (f₂ : W' ≃L[ℂ] W'') (a : Symbol n V W m) :
    transport A e₂ f₂ (transport B e₁ f₁ a) =
      transport (B.trans A) (e₁.trans e₂) (f₁.trans f₂) a := by
  refine Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ ?_)
  simp [ContinuousLinearEquiv.adjointEquiv_apply, ← ContinuousLinearEquiv.comp_coe,
    ContinuousLinearMap.adjoint_comp]

/-- For automorphisms, transport turns products into composites, so a group homomorphism into the
linear symmetries gives an action on symbols. -/
theorem transport_mul (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e e' : V ≃L[ℂ] V)
    (f f' : W ≃L[ℂ] W) (a : Symbol n V W m) :
    transport (A * B) (e * e') (f * f') a = transport A e f (transport B e' f' a) := by
  simp only [ContinuousLinearEquiv.mul_eq_trans, transport_transport]

/-- Transport is the linear change of variables `(y, η) ↦ (A⁻¹ y, Aᵀ η)` followed by the change
`T ↦ f ∘ T ∘ e⁻¹` of coefficients. -/
theorem transport_eq_map_compProdMap (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) :
    transport A e f a = (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      A.adjointEquiv a).map ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ) := by
  rw [transport]

/-- The mixed derivatives of a transported symbol are the conjugated mixed derivatives of the
symbol with the positions and frequencies changed. -/
theorem mixedDeriv_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (transport A e f a).coefficient x ξ =
      (f : W →L[ℂ] W') ∘L mixedDeriv α β (a.coefficient ∘
        (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
          (A.adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)) x ξ ∘L
            (e.symm : V' →L[ℂ] V) := by
  rw [coefficient_transport_eq_comp, ContinuousLinearMap.mixedDeriv_comp_left _
    (a.contDiff_coefficient.comp (ContinuousLinearMap.contDiff _))]
  ext v
  simp

/-- Transport commutes with the inclusion of symbol classes. -/
@[simp]
theorem transport_inclusion {m' : ℝ} (h : m ≤ m') (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) :
    transport A e f (inclusion h a) = inclusion h (transport A e f a) :=
  Symbol.ext (funext fun _ ↦ by simp [coefficient_inclusion])

/-- Transport preserves smoothing symbols. -/
theorem IsSmoothing.transport {a : Symbol n V W m} (ha : a.IsSmoothing)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') :
    (Symbol.transport A e f a).IsSmoothing :=
  (ha.compProdMap _ _).map _

/-- Transport preserves estimates uniform in the position. -/
theorem IsUniform.transport {a : Symbol n V W m} (ha : a.IsUniform)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') :
    (Symbol.transport A e f a).IsUniform :=
  (ha.compProdMap _ _).map _

/-- Transport preserves compact spatial support: if `a` vanishes outside `K`, its transport
vanishes outside `A K`. -/
theorem HasCompactSpatialSupport.transport {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') : (Symbol.transport A e f a).HasCompactSpatialSupport :=
  (ha.compProdMap A.symm A.adjointEquiv).map _

open scoped FourierTransform

/-- **Quantization of a transported symbol.** Quantizing the transport of `a` along `(A, e, f)`
conjugates `Op(a)` by the actions `u ↦ e ∘ u ∘ A⁻¹` on inputs and `w ↦ f ∘ w ∘ A⁻¹` on outputs:
`Op(transport A e f a)(e ∘ v ∘ A⁻¹)(y) = f (Op(a) v (A⁻¹ y))`. -/
theorem quantizeSchwartzValue_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (v : 𝓢(CoordinateSpace n, V))
    (y : CoordinateSpace n) :
    quantizeSchwartzValue (transport A e f a).coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm v).postcompCLM (e : V →L[ℂ] V')) y =
      f (quantizeSchwartzValue a.coefficient v (A.symm y)) := by
  have hv : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm v) = v := by
    ext x
    simp
  rw [quantizeSchwartzValue_congr_left (b := fun p ↦ e.arrowCongr f
      ((compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
        a).coefficient p)) (fun _ ↦ by rw [transport, coefficient_map_arrowCongr]),
    quantizeSchwartzValue_arrowCongr, ← A.apply_symm_apply y,
    quantizeSchwartzValue_compProdMap_symm_adjointEquiv, hv, A.apply_symm_apply]

/-- **Invariant symbols quantize to equivariant operators.** If the transport of `a` along
`(A, e, f)` is `a`, then `Op(a)(e ∘ v ∘ A⁻¹)(y) = f (Op(a) v (A⁻¹ y))`. -/
theorem quantizeSchwartzValue_of_transport_eq {A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n}
    {e : V ≃L[ℂ] V} {f : W ≃L[ℂ] W} {a : Symbol n V W m} (ha : transport A e f a = a)
    (v : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm v).postcompCLM (e : V →L[ℂ] V)) y =
      f (quantizeSchwartzValue a.coefficient v (A.symm y)) := by
  conv_lhs => rw [← ha]
  exact quantizeSchwartzValue_transport A e f a v y

/-- **Invariant symbols quantize to equivariant operators**, in terms of the representation
`TauCeti.schwartzRep` on Schwartz functions: if `a` is invariant under the action of `G`, then
`Op(a)(g • u)(ρ(g) x) = τ(g) (Op(a) u x)`. -/
theorem quantizeSchwartzValue_schwartzRep {G : Type*} [Group G]
    {ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)} {σ : G →* (V ≃L[ℂ] V)}
    {τ : G →* (W ≃L[ℂ] W)} {a : Symbol n V W m} (ha : ∀ g, transport (ρ g) (σ g) (τ g) a = a)
    (g : G) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (schwartzRep ρ σ g u) (ρ g x) =
      τ g (quantizeSchwartzValue a.coefficient u x) := by
  have hrep : schwartzRep ρ σ g u =
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm u).postcompCLM
        (σ g : V →L[ℂ] V) := by
    ext y
    simp
  rw [hrep, quantizeSchwartzValue_of_transport_eq (ha g), ContinuousLinearEquiv.symm_apply_apply]

/-- The quantization of a transported symbol on an arbitrary input `u`: at `y` it is
`f (Op(a) (e⁻¹ ∘ u ∘ A) (A⁻¹ y))`. -/
theorem quantizeSchwartzValue_transport_apply (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V'))
    (y : CoordinateSpace n) :
    quantizeSchwartzValue (transport A e f a).coefficient u y =
      f (quantizeSchwartzValue a.coefficient
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (u.postcompCLM (e.symm : V' →L[ℂ] V)))
        (A.symm y)) := by
  have hu : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
        (u.postcompCLM (e.symm : V' →L[ℂ] V)))).postcompCLM (e : V →L[ℂ] V') = u := by
    ext z
    simp
  rw [← quantizeSchwartzValue_transport A e f a, hu]

end Transport

section Average

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G] [CompactSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
  (ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)) (σ : G →* (V ≃L[ℂ] V))
  (τ : G →* (W ≃L[ℂ] W))

variable {ρ σ τ}
variable (hρ : Continuous fun g ↦ (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n))
  (hσ : Continuous fun g ↦ (σ g : V →L[ℂ] V)) (hτ : Continuous fun g ↦ (τ g : W →L[ℂ] W))

omit [CompactSpace G] [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- The jets of the transported symbols `g • a` are jointly continuous in `g` and the
position-frequency variables. -/
private theorem continuous_iteratedFDeriv_transport (a : Symbol n V W m) (k : ℕ) :
    Continuous fun q : G × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (transport (ρ q.1) (σ q.1) (τ q.1) a).coefficient q.2 := by
  -- All transported coefficients are slices of one smooth function of the parameters
  -- `(P, Q, L, R)` and of `(x, ξ)`, namely `L ∘ a(P x, Q ξ) ∘ R`.
  let U : (((CoordinateSpace n →L[ℝ] CoordinateSpace n) ×
      (CoordinateSpace n →L[ℝ] CoordinateSpace n)) × ((W →L[ℂ] W) × (V →L[ℂ] V))) ×
      (CoordinateSpace n × CoordinateSpace n) → V →L[ℂ] W :=
    fun z ↦ z.1.2.1 ∘L a.coefficient (z.1.1.1 z.2.1, z.1.1.2 z.2.2) ∘L z.1.2.2
  -- Composition of `ℂ`-linear maps, viewed as a continuous `ℝ`-bilinear map, is smooth.
  have hU : ContDiff ℝ ∞ U :=
    (((ContinuousLinearMap.compL ℂ V W W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff
      (n := ∞)).comp (contDiff_fst.snd.fst.prodMk
      ((((ContinuousLinearMap.compL ℂ V V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap
        |>.contDiff (n := ∞)).comp ((a.contDiff_coefficient.comp
          ((contDiff_fst.fst.fst.clm_apply contDiff_snd.fst).prodMk
            (contDiff_fst.fst.snd.clm_apply contDiff_snd.snd))).prodMk contDiff_fst.snd.snd)))
  have hpar : Continuous fun g ↦ ((((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n),
      ((ρ g).adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)),
      ((τ g : W →L[ℂ] W), ((σ g).symm : V →L[ℂ] V))) := by
    exact (hρ.continuous_symm_of_monoidHom.prodMk
      (ContinuousLinearEquiv.continuous_adjointEquiv hρ)).prodMk
      (hτ.prodMk hσ.continuous_symm_of_monoidHom)
  refine ((hU.continuous_iteratedFDeriv_prod_right k (by simp)).comp
    ((hpar.comp continuous_fst).prodMk continuous_snd)).congr fun q ↦ ?_
  have hfun : (fun y ↦ U (((((ρ q.1).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n),
      ((ρ q.1).adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)),
      ((τ q.1 : W →L[ℂ] W), ((σ q.1).symm : V →L[ℂ] V))), y)) =
      (transport (ρ q.1) (σ q.1) (τ q.1) a).coefficient :=
    funext fun y ↦ (coefficient_transport _ _ _ _ y).symm
  simp only [Function.comp_apply, hfun]

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- **Uniform estimates for transported symbols.** If `a` satisfies the estimates of order `m`
with constants `C α' β'` at every position of a set `S`, then all the transported symbols `g • a`
satisfy the estimate for `(α, β)`, with one constant, at every position `x` with
`ρ(g)⁻¹ x ∈ S`. -/
private theorem exists_bound_mixedDeriv_transport (a : Symbol n V W m)
    {S : Set (CoordinateSpace n)} (C : List (Fin n) → List (Fin n) → ℝ)
    (hC : ∀ α' β', ∀ y ∈ S, ∀ η, ‖mixedDeriv α' β' a.coefficient y η‖ ≤
      C α' β' * (1 + ‖η‖ ^ 2) ^ ((m - β'.length) / 2)) (α β : List (Fin n)) :
    ∃ B, 0 ≤ B ∧ ∀ g x, (ρ g).symm x ∈ S → ∀ ξ,
      ‖mixedDeriv α β (transport (ρ g) (σ g) (τ g) a).coefficient x ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- The three actions are bounded in norm on the compact group, by the sup norms `Cρ`, `Cσ`, `Cτ`.
  set Cρ := ‖BoundedContinuousFunction.mkOfCompact ⟨_, hρ⟩‖
  set Cσ := ‖BoundedContinuousFunction.mkOfCompact ⟨_, hσ.continuous_symm_of_monoidHom⟩‖
  set Cτ := ‖BoundedContinuousFunction.mkOfCompact ⟨_, hτ⟩‖
  set c : ℝ := max 1 Cρ
  have hρc (g : G) : ‖(ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ ≤ c :=
    ((BoundedContinuousFunction.mkOfCompact ⟨_, hρ⟩).norm_coe_le_norm g).trans (le_max_right _ _)
  obtain ⟨B, hB0, hB⟩ :=
    exists_bound_mixedDeriv_comp_prodMap (m := m) a.contDiff_coefficient (le_max_left 1 Cρ) C α β
  refine ⟨Cτ * B * Cσ, by positivity, fun g x hx ξ ↦ ?_⟩
  -- The position map is `ρ(g⁻¹)` and the frequency map is the adjoint of `ρ(g)`, with inverse the
  -- adjoint of `ρ(g⁻¹)`; all three have norm at most `c`.
  have hsymm : ‖((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ ≤ c := by
    simpa only [map_inv, ContinuousLinearEquiv.inv_eq_symm] using hρc g⁻¹
  have hinv (ξ : CoordinateSpace n) : ‖ξ‖ ≤ c * ‖(ρ g).adjointEquiv ξ‖ := by
    calc ‖ξ‖ = ‖((ρ g).adjointEquiv.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
          ((ρ g).adjointEquiv ξ)‖ := by
          rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖((ρ g).adjointEquiv.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)‖ *
          ‖(ρ g).adjointEquiv ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖(ρ g).adjointEquiv ξ‖ := by
          gcongr
          rwa [ContinuousLinearEquiv.adjointEquiv_symm, ContinuousLinearEquiv.norm_adjointEquiv]
  have hM := hB _ _ hsymm ((ContinuousLinearEquiv.norm_adjointEquiv _).trans_le (hρc g)) hinv
    x (fun α' β' η ↦ hC α' β' _ hx η) ξ
  rw [coefficient_transport_eq_comp, ContinuousLinearMap.mixedDeriv_comp_left _
    (a.contDiff_coefficient.comp (ContinuousLinearMap.contDiff _))]
  calc ‖(τ g : W →L[ℂ] W) ∘L mixedDeriv α β (a.coefficient ∘ _) x ξ ∘L
        ((σ g).symm : V →L[ℂ] V)‖
      ≤ ‖(τ g : W →L[ℂ] W)‖ * ‖mixedDeriv α β (a.coefficient ∘ _) x ξ‖ *
          ‖((σ g).symm : V →L[ℂ] V)‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by rw [mul_assoc]; gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ Cτ * (B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) * Cσ := by
        gcongr
        exacts [(BoundedContinuousFunction.mkOfCompact ⟨_, hτ⟩).norm_coe_le_norm g,
          (BoundedContinuousFunction.mkOfCompact ⟨_, hσ.continuous_symm_of_monoidHom⟩
            ).norm_coe_le_norm g]
    _ = _ := by ring

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
include hρ hσ hτ in
/-- The transported symbols `g • a` satisfy the estimates of order `m` on each compact set of
positions with constants independent of `g`. -/
private theorem exists_bound_transport (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ B, 0 ≤ B ∧ ∀ g, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (transport (ρ g) (σ g) (τ g) a).coefficient x ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- The positions `ρ(g)⁻¹ x` with `x ∈ K` form the compact set `S`.
  set S := (fun q : G × CoordinateSpace n ↦ (ρ q.1).symm q.2) '' (Set.univ ×ˢ K)
  have hS : IsCompact S := (isCompact_univ.prod hK).image
    ((hρ.continuous_symm_of_monoidHom.comp continuous_fst).clm_apply continuous_snd)
  choose C _ hC using fun α' β' ↦ a.exists_bound S hS α' β'
  obtain ⟨B, hB0, hB⟩ := exists_bound_mixedDeriv_transport hρ hσ hτ a C hC α β
  exact ⟨B, hB0, fun g x hx ξ ↦ hB g x ⟨(g, x), ⟨Set.mem_univ _, hx⟩, rfl⟩ ξ⟩

/-- **The average of a symbol over a compact group.** For a compact group `G` acting continuously
by `ρ` on `ℝⁿ` and by `σ`, `τ` on `V`, `W`, and a finite measure `μ` on `G`, the symbol
`∫ g • a dμ(g)` of order `m`, where `(g • a)(x, ξ) = τ(g) ∘ a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) ∘ σ(g)⁻¹`
(`TauCeti.Symbol.transport`). For the normalized Haar measure this is the Haar average, which is
invariant (`TauCeti.Symbol.transport_average`) and fixes invariant symbols
(`TauCeti.Symbol.average_eq_self`). -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  integral μ (fun g ↦ transport (ρ g) (σ g) (τ g) a)
    (continuous_iteratedFDeriv_transport hρ hσ hτ a) (exists_bound_transport hρ hσ hτ a)

/-- The coefficient of the average is the average of the transported coefficients. -/
@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ hρ hσ hτ a).coefficient p =
      ∫ g, (τ g : W →L[ℂ] W) ∘L a.coefficient ((ρ g).symm p.1, (ρ g).adjointEquiv p.2) ∘L
        ((σ g).symm : V →L[ℂ] V) ∂μ := by
  simp only [average, coefficient_integral, coefficient_transport]

@[simp]
theorem average_zero : average μ hρ hσ hτ (0 : Symbol n V W m) = 0 :=
  Symbol.ext (funext fun p ↦ by simp)

/-- Averaging is additive. -/
theorem average_add (a b : Symbol n V W m) :
    average μ hρ hσ hτ (a + b) = average μ hρ hσ hτ a + average μ hρ hσ hτ b := by
  simp only [average, transport_add]
  exact integral_add μ _ _ (continuous_iteratedFDeriv_transport hρ hσ hτ a)
    (continuous_iteratedFDeriv_transport hρ hσ hτ b)

/-- Averaging commutes with multiplication by complex scalars. -/
theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ hρ hσ hτ (c • a) = c • average μ hρ hσ hτ a := by
  simp only [average, transport_smul]
  exact integral_smul μ c _ (continuous_iteratedFDeriv_transport hρ hσ hτ a)

/-- The coefficient of the average depends only on the coefficient of the symbol, so averaging
commutes with the inclusions of symbol classes. -/
@[simp]
theorem average_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    average μ hρ hσ hτ (inclusion h a) = inclusion h (average μ hρ hσ hτ a) :=
  Symbol.ext (funext fun p ↦ by simp [coefficient_inclusion])

/-- **Seminorm control.** A bound `C` on the seminorm `p_{K,α,β}` of the transported symbols
`g • a`, uniform in `g`, bounds the seminorm of the average by `μ(G) C`. -/
theorem seminorm_average_le (a : Symbol n V W m) (K : TopologicalSpace.Compacts (CoordinateSpace n))
    (α β : List (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ g, Symbol.seminorm K α β (transport (ρ g) (σ g) (τ g) a) ≤ C) :
    Symbol.seminorm K α β (average μ hρ hσ hτ a) ≤ μ.real Set.univ * C :=
  seminorm_integral_le μ _ _ _ K α β hC h

/-- **Seminorm control.** Averaging over a probability measure preserves every bound on the
seminorm `p_{K,α,β}` of the transported symbols `g • a` that is uniform in `g`. -/
theorem seminorm_average_le_of_probability [IsProbabilityMeasure μ] (a : Symbol n V W m)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ g, Symbol.seminorm K α β (transport (ρ g) (σ g) (τ g) a) ≤ C) :
    Symbol.seminorm K α β (average μ hρ hσ hτ a) ≤ C :=
  seminorm_integral_le_of_probability μ _ _ _ K α β hC h

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- **The average is invariant.** For a left-invariant measure, transporting the average along
the action of any `h ∈ G` gives the average back. -/
theorem transport_average (a : Symbol n V W m) (h : G) :
    transport (ρ h) (σ h) (τ h) (average μ hρ hσ hτ a) = average μ hρ hσ hτ a := by
  refine Symbol.ext (funext fun p ↦ ?_)
  -- Conjugation by `σ(h)`, `τ(h)` passes through the integral; then the transports compose and
  -- the measure is invariant under `g ↦ h g`.
  have hconj (T : V →L[ℂ] W) : (τ h : W →L[ℂ] W) ∘L T ∘L ((σ h).symm : V →L[ℂ] V) =
      (σ h).arrowCongr (τ h) T :=
    ContinuousLinearMap.ext fun v ↦ by simp
  have hgh (g : G) : (σ h).arrowCongr (τ h) ((transport (ρ g) (σ g) (τ g) a).coefficient
      ((ρ h).symm p.1, (ρ h).adjointEquiv p.2)) =
      (transport (ρ (h * g)) (σ (h * g)) (τ (h * g)) a).coefficient p := by
    rw [← hconj, ← coefficient_transport, map_mul, map_mul, map_mul, transport_mul]
  calc (transport (ρ h) (σ h) (τ h) (average μ hρ hσ hτ a)).coefficient p
      = (σ h).arrowCongr (τ h) (∫ g, (transport (ρ g) (σ g) (τ g) a).coefficient
          ((ρ h).symm p.1, (ρ h).adjointEquiv p.2) ∂μ) := by
        rw [coefficient_transport, ← hconj, average, coefficient_integral]
    _ = ∫ g, (transport (ρ (h * g)) (σ (h * g)) (τ (h * g)) a).coefficient p ∂μ := by
        rw [← ContinuousLinearEquiv.integral_comp_comm]
        exact integral_congr_ae (Filter.Eventually.of_forall hgh)
    _ = ∫ g, (transport (ρ g) (σ g) (τ g) a).coefficient p ∂μ :=
        integral_mul_left_eq_self (fun g ↦ (transport (ρ g) (σ g) (τ g) a).coefficient p) h
    _ = (average μ hρ hσ hτ a).coefficient p := by rw [average, coefficient_integral]

open scoped FourierTransform in
/-- **The averaged operator is equivariant.** For a left-invariant measure, the quantization of
the average commutes with the actions `u ↦ σ(h) ∘ u ∘ ρ(h)⁻¹` on inputs and
`w ↦ τ(h) ∘ w ∘ ρ(h)⁻¹` on outputs. -/
theorem quantizeSchwartzValue_average_transport (a : Symbol n V W m) (h : G)
    (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n) :
    quantizeSchwartzValue (average μ hρ hσ hτ a).coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ h).symm u).postcompCLM
          (σ h : V →L[ℂ] V)) y =
      τ h (quantizeSchwartzValue (average μ hρ hσ hτ a).coefficient u ((ρ h).symm y)) :=
  quantizeSchwartzValue_of_transport_eq (transport_average μ hρ hσ hτ a h) u y

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- **The averaged operator is the average of the conjugated operators.** On a Schwartz input `u`,
`Op(avg a) u (x) = ∫ τ(g) (Op(a)(σ(g)⁻¹ ∘ u ∘ ρ(g)) (ρ(g)⁻¹ x)) dμ(g)`. -/
theorem quantizeSchwartzValue_average (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (average μ hρ hσ hτ a).coefficient u x =
      ∫ g, τ g (quantizeSchwartzValue a.coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g) u).postcompCLM
          ((σ g).symm : V →L[ℂ] V)) ((ρ g).symm x)) ∂μ := by
  rw [average, quantizeSchwartzValue_integral]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  have hu : ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g).symm
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g) u).postcompCLM
        ((σ g).symm : V →L[ℂ] V))).postcompCLM (σ g : V →L[ℂ] V)) = u := by
    ext y
    simp
  dsimp only
  rw [← quantizeSchwartzValue_transport (ρ g) (σ g) (τ g), hu]

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- **Averaging an invariant symbol.** A symbol invariant under the action of every `g ∈ G`
averages to its multiple by the total mass of `μ`. -/
theorem average_eq_smul_self [CompleteSpace (V →L[ℂ] W)] {a : Symbol n V W m}
    (ha : ∀ g, transport (ρ g) (σ g) (τ g) a = a) :
    average μ hρ hσ hτ a = (μ.real Set.univ : ℂ) • a := by
  simp only [average, ha]
  exact integral_const μ a

omit [MeasurableMul G] [μ.IsMulLeftInvariant] in
/-- **Averaging fixes invariant symbols.** For a probability measure, a symbol invariant under
the action of every `g ∈ G` is its own average. -/
theorem average_eq_self [CompleteSpace (V →L[ℂ] W)] [IsProbabilityMeasure μ]
    {a : Symbol n V W m} (ha : ∀ g, transport (ρ g) (σ g) (τ g) a = a) :
    average μ hρ hσ hτ a = a := by
  rw [average_eq_smul_self μ hρ hσ hτ ha, probReal_univ, Complex.ofReal_one, one_smul]

/-- **Averaging is idempotent** for a left-invariant probability measure. -/
@[simp]
theorem average_average [CompleteSpace (V →L[ℂ] W)] [IsProbabilityMeasure μ]
    (a : Symbol n V W m) :
    average μ hρ hσ hτ (average μ hρ hσ hτ a) = average μ hρ hσ hτ a :=
  average_eq_self μ hρ hσ hτ (transport_average μ hρ hσ hτ a)

/-- For a left-invariant probability measure, such as the normalized Haar measure, a symbol is
its own average exactly when it is invariant under the action of every `g ∈ G`. -/
theorem average_eq_self_iff [CompleteSpace (V →L[ℂ] W)] [IsProbabilityMeasure μ]
    {a : Symbol n V W m} :
    average μ hρ hσ hτ a = a ↔ ∀ g, transport (ρ g) (σ g) (τ g) a = a :=
  ⟨fun h g ↦ by rw [← h]; exact transport_average μ hρ hσ hτ a g, average_eq_self μ hρ hσ hτ⟩

omit [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The average of a smoothing symbol is smoothing. -/
theorem IsSmoothing.average {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (Symbol.average μ hρ hσ hτ a).IsSmoothing := by
  refine isSmoothing_iff.2 fun m' ↦ ?_
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.average μ hρ hσ hτ b, funext fun p ↦ by simp [hb]⟩

/-- The average of a symbol with estimates uniform in the position has estimates uniform in the
position. -/
theorem IsUniform.average {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.average μ hρ hσ hτ a).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  choose C _ hC using isUniform_iff.1 ha
  obtain ⟨B, hB0, hB⟩ := exists_bound_mixedDeriv_transport hρ hσ hτ a (S := Set.univ) C
    (fun α' β' y _ η ↦ hC α' β' y η) α β
  refine ⟨μ.real Set.univ * B, mul_nonneg measureReal_nonneg hB0, fun x ξ ↦ ?_⟩
  have hcoef : (Symbol.average μ hρ hσ hτ a).coefficient =
      fun p ↦ ∫ g, (Symbol.transport (ρ g) (σ g) (τ g) a).coefficient p ∂μ :=
    funext fun p ↦ by rw [Symbol.average, coefficient_integral]
  rw [hcoef]
  exact norm_mixedDeriv_integral_le μ _ (continuous_iteratedFDeriv_transport hρ hσ hτ a) α β x ξ
    fun g ↦ hB g x (Set.mem_univ _) ξ

/-- The average of a symbol with compact spatial support has compact spatial support: if `a`
vanishes at positions outside `K`, its average vanishes outside the compact set `ρ(G) K`. -/
theorem HasCompactSpatialSupport.average {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) :
    (Symbol.average μ hρ hσ hτ a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2
    ⟨(fun q : G × CoordinateSpace n ↦ ρ q.1 q.2) '' (Set.univ ×ˢ K),
      (isCompact_univ.prod hK).image ((hρ.comp continuous_fst).clm_apply continuous_snd),
      fun x hx ξ ↦ ?_⟩
  rw [coefficient_average]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)).trans
    (MeasureTheory.integral_zero _ _)
  have hg : (ρ g).symm x ∉ K := fun hgx ↦ hx ⟨(g, (ρ g).symm x), ⟨Set.mem_univ _, hgx⟩, by simp⟩
  simp [hKa _ hg]

end Average

end Symbol

end TauCeti
