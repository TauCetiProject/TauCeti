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
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
import TauCeti.Topology.Algebra.Module.Equiv.Automorphism

/-!
# Averaging symbols over a compact group of linear symmetries

Let a group `G` act on `ℝⁿ` by linear automorphisms `ρ(g)` and on the coefficient spaces `V` and
`W` by isomorphisms `σ_V(g)` and `σ_W(g)`. It acts on functions `u : ℝⁿ → V` by
`(g · u)(x) = σ_V(g) u(ρ(g)⁻¹ x)`, and on operators by conjugation `g · T = g ∘ T ∘ g⁻¹`. This
file shows that conjugation preserves the quantizations of symbols of order `m`, and that for a
compact group the average of the conjugates of `Op(a)` is the quantization of an invariant symbol
of order `m`, so that averaging produces equivariant pseudodifferential operators.

## Transport along linear symmetries

For a linear automorphism `A` of `ℝⁿ` and isomorphisms `e : V ≃ V'`, `f : W ≃ W'`, the
**transported symbol** (`TauCeti.Symbol.transport`) is

`(A, e, f) · a (y, η) = f ∘ a(A⁻¹ y, Aᵀ η) ∘ e⁻¹`.

Positions move by `A` and frequencies, being covectors, by the inverse transpose. It is again a
symbol of order `m`, and it is the symbol of the conjugated operator: quantizing it on the
transported input `e ∘ u ∘ A⁻¹` gives the transported output `f ∘ Op(a) u ∘ A⁻¹`
(`TauCeti.Symbol.quantizeSchwartzValue_transport`). This combines the exact linear change of
coordinates formula of `TauCeti.Symbol.quantizeSchwartzValue_compProdMap_symm_adjointEquiv` with the
change of coefficient spaces `TauCeti.quantizeSchwartzValue_arrowCongr`. Transport is functorial
(`TauCeti.Symbol.transport_transport`), so a group homomorphism into the linear symmetries gives
an action of the group on symbols (`TauCeti.Symbol.transport_mul`). As a linear change of
variables followed by a change of coefficients (`TauCeti.Symbol.transport_eq_map_compProdMap`),
transport preserves smoothing symbols, uniform estimates and compact spatial support
(`TauCeti.Symbol.IsSmoothing.transport`, `TauCeti.Symbol.IsUniform.transport`,
`TauCeti.Symbol.HasCompactSpatialSupport.transport`), and its mixed derivatives are those of `a`
with the variables changed and the coefficients conjugated (`TauCeti.Symbol.mixedDeriv_transport`).

## Averaging

Now let `G` be a compact group with continuous inversion and a finite measure `μ`, typically the
normalized Haar measure, and let `ρ`, `σ_V`, `σ_W` be continuous in the operator norm. The
**average** (`TauCeti.Symbol.average`) of a symbol `a` of order `m` is the symbol of order `m`

`ā (x, ξ) = ∫ σ_W(g) a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) σ_V(g)⁻¹ dμ(g)`.

It is a symbol by `TauCeti.Symbol.integral`: the spatial jets of the conjugates are jointly
continuous in `g` and the position-frequency variables, and the symbol estimates of the conjugates
hold with constants independent of `g`, because the norms of `ρ(g)^{±1}`, `ρ(g)^{±T}` and
`σ(g)^{±1}` are bounded over the compact group (`TauCeti.Symbol.exists_bound_comp_prodMap`).

* `TauCeti.Symbol.quantizeSchwartzValue_average`: the quantization of `ā` is the average of the
  conjugates of `Op(a)`, `Op(ā) u = ∫ g · Op(a) (g⁻¹ · u) dμ(g)`.
* `TauCeti.Symbol.transport_average`: for a left-invariant measure, `ā` is invariant, and
  `TauCeti.Symbol.quantizeSchwartzValue_average_postcompCLM`: `Op(ā)` is equivariant,
  `Op(ā) (g · u) = g · Op(ā) u`.
* `TauCeti.Symbol.average_eq_self`: for a probability measure, an invariant symbol is its own
  average, so for normalized Haar measure averaging is a projection onto the invariant symbols
  (`TauCeti.Symbol.average_average`). For the trivial group it is the identity.
* `TauCeti.Symbol.seminorm_average_le`: for a probability measure, a seminorm bound shared by all
  conjugates of `a` holds for `ā`.
* `TauCeti.Symbol.IsSmoothing.average`, `TauCeti.Symbol.IsUniform.average`,
  `TauCeti.Symbol.HasCompactSpatialSupport.average`: averaging preserves smoothing symbols, symbols
  with estimates uniform in the position, and compact spatial support.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  (5.5)–(5.6), pp. 516–517: averaging pseudodifferential operators over a compact group.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1,
  Theorem 18.1.17: the change of variables formula, which is exact for linear changes.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W V' W' V'' W'' : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
  [NormedAddCommGroup V''] [NormedSpace ℂ V''] [NormedAddCommGroup W''] [NormedSpace ℂ W'']
  {m : ℝ}

/-! ### Transport along a linear symmetry -/

section Transport

/-- The symbol `(y, η) ↦ f ∘ a(A⁻¹ y, Aᵀ η) ∘ e⁻¹` of order `m`: the symbol `a` transported along
the linear automorphism `A` of positions and the isomorphisms `e`, `f` of the coefficient spaces.
Its quantization is `Op(a)` conjugated by these symmetries
(`TauCeti.Symbol.quantizeSchwartzValue_transport`). -/
def transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') :
    Symbol n V W m →ₗ[ℂ] Symbol n V' W' m where
  toFun a := (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
    a).map ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ)
  map_add' a b := Symbol.ext (funext fun p ↦ by simp)
  map_smul' c a := Symbol.ext (funext fun p ↦ by simp)

@[simp]
theorem coefficient_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V')
    (f : W ≃L[ℂ] W') (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (transport A e f a).coefficient p =
      e.arrowCongr f (a.coefficient (A.symm p.1, A.adjointEquiv p.2)) := by
  simp [transport]

/-- Transport is the linear change of variables `(y, η) ↦ (A⁻¹ y, Aᵀ η)` followed by the change
`T ↦ f ∘ T ∘ e⁻¹` of coefficients. -/
theorem transport_eq_map_compProdMap (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) :
    transport A e f a = (compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n)
      A.adjointEquiv a).map ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ) :=
  Symbol.ext (funext fun _ ↦ by simp)

/-- The mixed derivatives of a transported symbol are the transported mixed derivatives of the
symbol with the positions and frequencies changed. -/
theorem mixedDeriv_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (transport A e f a).coefficient x ξ =
      (f : W →L[ℂ] W').comp ((mixedDeriv α β (a.coefficient ∘
        (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
          (A.adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)) x ξ).comp
            (e.symm : V' →L[ℂ] V)) := by
  set L := (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
    (A.adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n)
  have h : (transport A e f a).coefficient =
      ((e.arrowCongr f).toContinuousLinearMap.restrictScalars ℝ) ∘ (a.coefficient ∘ L) :=
    funext fun p ↦ by simp [L, Prod.map]
  rw [h, ContinuousLinearMap.mixedDeriv_comp_left _
    (a.contDiff_coefficient.comp L.contDiff) α β x ξ]
  ext v
  simp

/-- Transporting along the identity symmetries leaves a symbol unchanged. -/
@[simp]
theorem transport_refl (a : Symbol n V W m) :
    transport (.refl ℝ (CoordinateSpace n)) (.refl ℂ V) (.refl ℂ W) a = a :=
  Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by
    simp [ContinuousLinearMap.adjoint_id])

/-- Transport is functorial: transporting along `(B, e₁, f₁)` and then along `(A, e₂, f₂)` is
transporting along the composites. -/
@[simp]
theorem transport_transport (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e₁ : V ≃L[ℂ] V')
    (e₂ : V' ≃L[ℂ] V'') (f₁ : W ≃L[ℂ] W') (f₂ : W' ≃L[ℂ] W'') (a : Symbol n V W m) :
    transport A e₂ f₂ (transport B e₁ f₁ a) = transport (B.trans A) (e₁.trans e₂) (f₁.trans f₂) a :=
  Symbol.ext (funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by
    simp [← ContinuousLinearEquiv.comp_coe, ContinuousLinearMap.adjoint_comp])

/-- Transporting along the identity automorphisms leaves a symbol unchanged. -/
@[simp]
theorem transport_one (a : Symbol n V W m) : transport 1 1 1 a = a := by
  simp only [ContinuousLinearEquiv.one_eq_refl, transport_refl]

/-- For automorphisms, transport turns products into composites, so a group homomorphism into the
linear symmetries gives an action on symbols. -/
theorem transport_mul (A B : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e e' : V ≃L[ℂ] V)
    (f f' : W ≃L[ℂ] W) (a : Symbol n V W m) :
    transport (A * B) (e * e') (f * f') a = transport A e f (transport B e' f' a) := by
  simp only [ContinuousLinearEquiv.mul_eq_trans, transport_transport]

/-- Transport commutes with the inclusion of symbol classes. -/
@[simp]
theorem transport_inclusion {m' : ℝ} (h : m ≤ m') (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) :
    transport A e f (inclusion h a) = inclusion h (transport A e f a) :=
  Symbol.ext (funext fun _ ↦ by simp)

/-- Transport preserves smoothing symbols. -/
theorem IsSmoothing.transport {a : Symbol n V W m} (ha : a.IsSmoothing)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') :
    (transport A e f a).IsSmoothing := by
  rw [transport_eq_map_compProdMap]
  exact (ha.compProdMap _ _).map _

/-- Transport preserves estimates uniform in the position. -/
theorem IsUniform.transport {a : Symbol n V W m} (ha : a.IsUniform)
    (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n) (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') :
    (transport A e f a).IsUniform := by
  rw [transport_eq_map_compProdMap]
  exact (ha.compProdMap _ _).map _

/-- Transport preserves compact spatial support: if `a` vanishes outside `K`, its transport
vanishes outside `A K`. -/
theorem HasCompactSpatialSupport.transport {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') : (transport A e f a).HasCompactSpatialSupport := by
  rw [transport_eq_map_compProdMap]
  exact (ha.compProdMap A.symm A.adjointEquiv).map _

/-- **Quantization of a transported symbol.** Quantizing the transported symbol on the transported
input `e ∘ u ∘ A⁻¹` gives the transported output: at `A x` it is `f (Op(a) u x)`. So
`Op((A, e, f) · a)` is `Op(a)` conjugated by the symmetries. -/
theorem quantizeSchwartzValue_transport (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (transport A e f a).coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u).postcompCLM (e : V →L[ℂ] V'))
        (A x) =
      f (quantizeSchwartzValue a.coefficient u x) := by
  have hu : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm u) = u := by
    ext y; simp
  rw [quantizeSchwartzValue_congr_left (b := fun p ↦ e.arrowCongr f
      ((compProdMap (A.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) A.adjointEquiv
        a).coefficient p)) (fun ξ ↦ by simp),
    quantizeSchwartzValue_arrowCongr, a.quantizeSchwartzValue_compProdMap_symm_adjointEquiv, hu]

/-- The quantization of a transported symbol on an arbitrary input `u`: at `y` it is
`f (Op(a) (e⁻¹ ∘ u ∘ A) (A⁻¹ y))`. -/
theorem quantizeSchwartzValue_transport_apply (A : CoordinateSpace n ≃L[ℝ] CoordinateSpace n)
    (e : V ≃L[ℂ] V') (f : W ≃L[ℂ] W') (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V'))
    (y : CoordinateSpace n) :
    quantizeSchwartzValue (transport A e f a).coefficient u y =
      f (quantizeSchwartzValue a.coefficient
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (u.postcompCLM (e.symm : V' →L[ℂ] V)))
        (A.symm y)) := by
  have hu : SchwartzMap.postcompCLM (e : V →L[ℂ] V')
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
          (SchwartzMap.postcompCLM (e.symm : V' →L[ℂ] V) u))) = u := by
    ext z; simp
  rw [← quantizeSchwartzValue_transport A e f a, hu, A.apply_symm_apply]

end Transport

/-! ### Averaging over a compact group -/

section Average

variable {G : Type*} [Group G] [TopologicalSpace G]
  (ρ : G →* (CoordinateSpace n ≃L[ℝ] CoordinateSpace n)) (σV : G →* (V ≃L[ℂ] V))
  (σW : G →* (W ≃L[ℂ] W))
  (hρ : Continuous fun g ↦ (ρ g : CoordinateSpace n →L[ℝ] CoordinateSpace n))
  (hσV : Continuous fun g ↦ (σV g : V →L[ℂ] V)) (hσW : Continuous fun g ↦ (σW g : W →L[ℂ] W))

variable [ContinuousInv G]

include hρ hσV hσW in
/-- The spatial jets of the conjugates of a symbol are jointly continuous in the group element and
the position-frequency variables. -/
private theorem continuous_iteratedFDeriv_transport (a : Symbol n V W m) (k : ℕ) :
    Continuous (fun z : G × (CoordinateSpace n × CoordinateSpace n) ↦
      iteratedFDeriv ℝ k (transport (ρ z.1) (σV z.1) (σW z.1) a).coefficient z.2) := by
  -- The conjugates are the slices of one smooth function of the matrices of the symmetries.
  let F : (((CoordinateSpace n × CoordinateSpace n) →L[ℝ] (CoordinateSpace n × CoordinateSpace n)) ×
      ((V →L[ℂ] V) × (W →L[ℂ] W))) × (CoordinateSpace n × CoordinateSpace n) → V →L[ℂ] W :=
    fun z ↦ (z.1.2.2.comp (a.coefficient (z.1.1 z.2))).comp z.1.2.1
  have hF : ContDiff ℝ ∞ F := by
    have ha : ContDiff ℝ ∞ fun z : (((CoordinateSpace n × CoordinateSpace n) →L[ℝ]
        (CoordinateSpace n × CoordinateSpace n)) × ((V →L[ℂ] V) × (W →L[ℂ] W))) ×
        (CoordinateSpace n × CoordinateSpace n) ↦ a.coefficient (z.1.1 z.2) :=
      a.contDiff_coefficient.comp (contDiff_fst.fst.clm_apply contDiff_snd)
    have hl := ((ContinuousLinearMap.compL ℂ V W W).bilinearRestrictScalars
      ℝ).isBoundedBilinearMap.contDiff.comp (contDiff_fst.snd.snd.prodMk ha)
    exact ((ContinuousLinearMap.compL ℂ V V W).bilinearRestrictScalars
      ℝ).isBoundedBilinearMap.contDiff.comp (hl.prodMk contDiff_fst.snd.fst)
  let κ : G → ((CoordinateSpace n × CoordinateSpace n) →L[ℝ]
      (CoordinateSpace n × CoordinateSpace n)) × ((V →L[ℂ] V) × (W →L[ℂ] W)) := fun g ↦
    (((ρ g).symm : CoordinateSpace n →L[ℝ] CoordinateSpace n).prodMap
      ((ρ g).adjointEquiv : CoordinateSpace n →L[ℝ] CoordinateSpace n),
      ((σV g).symm : V →L[ℂ] V), (σW g : W →L[ℂ] W))
  have hκ : Continuous κ := by
    refine Continuous.prodMk ?_ ((σV.continuous_coe_symm hσV).prodMk hσW)
    exact (ContinuousLinearMap.prodMapL ℝ _ _ _ _).continuous.comp
      ((ρ.continuous_coe_symm hρ).prodMk (ContinuousLinearEquiv.continuous_coe_adjointEquiv hρ))
  have hcoeff (g : G) : (transport (ρ g) (σV g) (σW g) a).coefficient = fun p ↦ F (κ g, p) :=
    funext fun p ↦ ContinuousLinearMap.ext fun v ↦ by simp [F, κ, Prod.map]
  simp_rw [hcoeff]
  exact (hF.continuous_iteratedFDeriv_prod_right k (mod_cast le_top)).comp
    ((hκ.comp continuous_fst).prodMk continuous_snd)

variable [CompactSpace G]

include hρ hσV hσW in
/-- If `a` has symbol estimates with constants `C` at all positions of a set `S` invariant under
the group, then its conjugates have symbol estimates at the positions of `S` with a constant
independent of the group element. -/
private theorem exists_bound_transport_of_forall_mem (a : Symbol n V W m)
    {S : Set (CoordinateSpace n)} (hS : ∀ g, ∀ x ∈ S, (ρ g).symm x ∈ S)
    (C : List (Fin n) → List (Fin n) → ℝ)
    (hC : ∀ α β, ∀ x ∈ S, ∀ ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C α β * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2))
    (α β : List (Fin n)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g, ∀ x ∈ S, ∀ ξ,
      ‖mixedDeriv α β (transport (ρ g) (σV g) (σW g) a).coefficient x ξ‖ ≤
        B * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- Bounds, uniform over the compact group, for the norms of the symmetries.
  have hbdd {φ : G → ℝ} (hφ : Continuous φ) : ∃ c, ∀ g, φ g ≤ c := by
    obtain ⟨c, hc⟩ := (isCompact_range hφ).bddAbove
    exact ⟨c, fun g ↦ hc ⟨g, rfl⟩⟩
  obtain ⟨c₁, hc₁⟩ := hbdd (ρ.continuous_coe_symm hρ).norm
  obtain ⟨c₂, hc₂⟩ := hbdd (ContinuousLinearEquiv.continuous_coe_adjointEquiv hρ).norm
  have hρ' : Continuous fun g ↦
      ((ρ g).adjointEquiv.symm : CoordinateSpace n →L[ℝ] CoordinateSpace n) := by
    simpa only [ContinuousLinearEquiv.adjointEquiv_symm] using
      ContinuousLinearEquiv.continuous_coe_adjointEquiv (f := fun g ↦ (ρ g).symm)
        (ρ.continuous_coe_symm hρ)
  obtain ⟨c₃, hc₃⟩ := hbdd hρ'.norm
  obtain ⟨d, hd⟩ := hbdd (hσW.norm.mul (σV.continuous_coe_symm hσV).norm)
  obtain ⟨B, hB, hB'⟩ := exists_bound_comp_prodMap a.contDiff_coefficient (max c₁ (max c₂ c₃)) C α β
  refine ⟨max d 0 * B, by positivity, fun g x hx ξ ↦ ?_⟩
  have hcomp (T : V →L[ℂ] W) : ‖(σW g : W →L[ℂ] W).comp (T.comp ((σV g).symm : V →L[ℂ] V))‖ ≤
      ‖(σW g : W →L[ℂ] W)‖ * ‖((σV g).symm : V →L[ℂ] V)‖ * ‖T‖ :=
    calc _ ≤ ‖(σW g : W →L[ℂ] W)‖ * (‖T‖ * ‖((σV g).symm : V →L[ℂ] V)‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact T.opNorm_comp_le _)
      _ = _ := by ring
  rw [mixedDeriv_transport]
  refine (hcomp _).trans ?_
  have hd' : ‖(σW g : W →L[ℂ] W)‖ * ‖((σV g).symm : V →L[ℂ] V)‖ ≤ max d 0 :=
    (hd g).trans (le_max_left _ _)
  refine (mul_le_mul hd' ?_ (norm_nonneg _) (le_max_right _ _)).trans_eq (mul_assoc _ _ _).symm
  exact hB' _ _ ((hc₁ g).trans (le_max_left _ _))
    ((hc₂ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    ((hc₃ g).trans ((le_max_right _ _).trans (le_max_right _ _))) x
    (fun α' β' η ↦ hC α' β' _ (hS g x hx) η) ξ

include hρ hσV hσW in
/-- The symbol estimates of the conjugates of a symbol on a compact set of positions, with
constants independent of the group element. -/
private theorem exists_bound_transport (a : Symbol n V W m) (K : Set (CoordinateSpace n))
    (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (transport (ρ g) (σV g) (σW g) a).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  -- The orbit of `K` is compact, and contains `K`.
  set S := (fun z : G × CoordinateSpace n ↦ (ρ z.1) z.2) '' (Set.univ ×ˢ K)
  have hcont : Continuous fun z : G × CoordinateSpace n ↦ (ρ z.1) z.2 :=
    (hρ.comp continuous_fst).clm_apply continuous_snd
  have hS : IsCompact S := (isCompact_univ.prod hK).image hcont
  have hKS : K ⊆ S := fun x hx ↦ ⟨(1, x), ⟨Set.mem_univ _, hx⟩,
    by simp [ContinuousLinearEquiv.one_eq_refl]⟩
  have hSinv : ∀ g, ∀ x ∈ S, (ρ g).symm x ∈ S := by
    rintro g _ ⟨⟨h, y⟩, ⟨-, hy⟩, rfl⟩
    exact ⟨(g⁻¹ * h, y), ⟨Set.mem_univ _, hy⟩,
      by simp [ContinuousLinearEquiv.mul_eq_trans, ContinuousLinearEquiv.inv_eq_symm]⟩
  choose C _ hC using fun α' β' ↦ a.exists_bound S hS α' β'
  obtain ⟨B, hB, hB'⟩ := exists_bound_transport_of_forall_mem ρ σV σW hρ hσV hσW a hSinv C hC α β
  exact ⟨B, hB, fun g x hx ξ ↦ hB' g x (hKS hx) ξ⟩

variable [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]

/-- The **average** of a symbol `a` over a compact group `G` acting linearly on the positions by
`ρ` and on the coefficient spaces by `σV` and `σW`, with respect to the finite measure `μ`:

`ā (x, ξ) = ∫ σW(g) a(ρ(g)⁻¹ x, ρ(g)ᵀ ξ) σV(g)⁻¹ dμ(g)`,

the integral of the transported symbols. It is a symbol of the same order. For the normalized Haar
measure it is invariant (`TauCeti.Symbol.transport_average`), and its quantization is the average
of the conjugates of `Op(a)` (`TauCeti.Symbol.quantizeSchwartzValue_average`). -/
def average : Symbol n V W m →ₗ[ℂ] Symbol n V W m where
  toFun a := integral μ (fun g ↦ transport (ρ g) (σV g) (σW g) a)
    (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW a)
    (fun K hK α β ↦ exists_bound_transport ρ σV σW hρ hσV hσW a K hK α β)
  map_add' a b := by
    simp only [map_add]
    exact Symbol.integral_add μ _ _ (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW a)
      (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW b)
  map_smul' c a := by
    simp only [map_smul, RingHom.id_apply]
    exact Symbol.integral_smul μ c _ (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW a)

/-- The coefficient of the average is the integral of the coefficients of the conjugates. -/
@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average ρ σV σW hρ hσV hσW μ a).coefficient p =
      ∫ g, (transport (ρ g) (σV g) (σW g) a).coefficient p ∂μ := by
  simp [average]

/-- **The averaged operator.** The quantization of the average of `a` is the average of the
conjugates `g · Op(a) · g⁻¹`: at `y` it is `∫ σW(g) Op(a) (σV(g)⁻¹ ∘ u ∘ ρ(g)) (ρ(g)⁻¹ y) dμ(g)`. -/
theorem quantizeSchwartzValue_average (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (y : CoordinateSpace n) :
    quantizeSchwartzValue (average ρ σV σW hρ hσV hσW μ a).coefficient u y =
      ∫ g, σW g (quantizeSchwartzValue a.coefficient
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ g)
          (u.postcompCLM ((σV g).symm : V →L[ℂ] V))) ((ρ g).symm y)) ∂μ := by
  rw [quantizeSchwartzValue_congr_left (b := (integral μ (fun g ↦ transport (ρ g) (σV g) (σW g) a)
      (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW a)
      (fun K hK α β ↦ exists_bound_transport ρ σV σW hρ hσV hσW a K hK α β)).coefficient)
      (fun ξ ↦ by simp), quantizeSchwartzValue_integral]
  simp_rw [quantizeSchwartzValue_transport_apply]

/-- The seminorm bound shared by all conjugates of `a` holds for its average with respect to a
probability measure. -/
theorem seminorm_average_le [IsProbabilityMeasure μ] (a : Symbol n V W m)
    (K : TopologicalSpace.Compacts (CoordinateSpace n)) (α β : List (Fin n)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ g, Symbol.seminorm K α β (transport (ρ g) (σV g) (σW g) a) ≤ C) :
    Symbol.seminorm K α β (average ρ σV σW hρ hσV hσW μ a) ≤ C :=
  seminorm_integral_le_of_probability μ _ _ _ K α β hC h

/-- For a left-invariant measure, the average is invariant under the group. -/
theorem transport_average [MeasurableMul G] [μ.IsMulLeftInvariant] (h : G) (a : Symbol n V W m) :
    transport (ρ h) (σV h) (σW h) (average ρ σV σW hρ hσV hσW μ a) =
      average ρ σV σW hρ hσV hσW μ a := by
  refine Symbol.ext (funext fun p ↦ ?_)
  rw [coefficient_transport, coefficient_average, coefficient_average,
    ← ContinuousLinearEquiv.integral_comp_comm]
  calc ∫ g, (σV h).arrowCongr (σW h) ((transport (ρ g) (σV g) (σW g) a).coefficient
          ((ρ h).symm p.1, (ρ h).adjointEquiv p.2)) ∂μ
      = ∫ g, (transport (ρ (h * g)) (σV (h * g)) (σW (h * g)) a).coefficient p ∂μ := by
        simp only [map_mul, transport_mul, coefficient_transport]
    _ = _ := integral_mul_left_eq_self (fun g ↦ (transport (ρ g) (σV g) (σW g) a).coefficient p) h

/-- **Equivariance of the averaged operator.** For a left-invariant measure, the quantization of
the average commutes with the group action `u ↦ σV(h) ∘ u ∘ ρ(h)⁻¹`. -/
theorem quantizeSchwartzValue_average_postcompCLM [MeasurableMul G] [μ.IsMulLeftInvariant] (h : G)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (average ρ σV σW hρ hσV hσW μ a).coefficient
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ρ h).symm u).postcompCLM
          (σV h : V →L[ℂ] V)) (ρ h x) =
      σW h (quantizeSchwartzValue (average ρ σV σW hρ hσV hσW μ a).coefficient u x) := by
  rw [← quantizeSchwartzValue_transport (ρ h) (σV h) (σW h), transport_average]

/-- For a probability measure, a symbol invariant under the group is its own average. For instance,
for the trivial action every symbol is its own average (`TauCeti.Symbol.transport_one`). -/
theorem average_eq_self [IsProbabilityMeasure μ] [CompleteSpace W] {a : Symbol n V W m}
    (ha : ∀ g, transport (ρ g) (σV g) (σW g) a = a) : average ρ σV σW hρ hσV hσW μ a = a := by
  refine Symbol.ext (funext fun p ↦ ?_)
  simp [ha]

/-- For a left-invariant probability measure, such as the normalized Haar measure, averaging is a
projection: the average of an average is itself. -/
theorem average_average [IsProbabilityMeasure μ] [MeasurableMul G] [μ.IsMulLeftInvariant]
    [CompleteSpace W]
    (a : Symbol n V W m) :
    average ρ σV σW hρ hσV hσW μ (average ρ σV σW hρ hσV hσW μ a) =
      average ρ σV σW hρ hσV hσW μ a :=
  average_eq_self ρ σV σW hρ hσV hσW μ fun g ↦ transport_average ρ σV σW hρ hσV hσW μ g a

/-- Averaging commutes with the inclusion of symbol classes. -/
@[simp]
theorem average_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    average ρ σV σW hρ hσV hσW μ (inclusion h a) = inclusion h (average ρ σV σW hρ hσV hσW μ a) :=
  Symbol.ext (funext fun _ ↦ by simp)

/-- The average of a smoothing symbol is smoothing. -/
theorem IsSmoothing.average {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (average ρ σV σW hρ hσV hσW μ a).IsSmoothing := by
  refine isSmoothing_iff.2 fun m' ↦ ?_
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  refine ⟨Symbol.average ρ σV σW hρ hσV hσW μ b, funext fun p ↦ ?_⟩
  simp [hb]

/-- The average of a symbol with estimates uniform in the position again has estimates uniform in
the position. -/
theorem IsUniform.average {a : Symbol n V W m} (ha : a.IsUniform) :
    (average ρ σV σW hρ hσV hσW μ a).IsUniform := by
  refine isUniform_iff.2 fun α β ↦ ?_
  choose C _ hC using isUniform_iff.1 ha
  obtain ⟨B, hB, hB'⟩ := exists_bound_transport_of_forall_mem ρ σV σW hρ hσV hσW a
    (S := Set.univ) (fun _ _ _ ↦ Set.mem_univ _) C (fun α β x _ ξ ↦ hC α β x ξ) α β
  refine ⟨μ.real Set.univ * B, by positivity, fun x ξ ↦ ?_⟩
  have h := seminorm_integral_le μ _ (continuous_iteratedFDeriv_transport ρ σV σW hρ hσV hσW a)
    (fun K hK α β ↦ exists_bound_transport ρ σV σW hρ hσV hσW a K hK α β)
    ⟨{x}, isCompact_singleton⟩ α β hB fun g ↦
      seminorm_le_bound _ α β _ hB fun y _ ξ ↦ hB' g y (Set.mem_univ y) ξ
  exact (le_seminorm _ α β _ (Set.mem_singleton x) ξ).trans
    (mul_le_mul_of_nonneg_right h (by positivity))

/-- The average of a symbol with compact spatial support has compact spatial support: it vanishes
outside the orbit of the support. -/
theorem HasCompactSpatialSupport.average {a : Symbol n V W m} (ha : a.HasCompactSpatialSupport) :
    (average ρ σV σW hρ hσV hσW μ a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  refine hasCompactSpatialSupport_iff.2 ⟨(fun z : G × CoordinateSpace n ↦ (ρ z.1) z.2) ''
    (Set.univ ×ˢ K), (isCompact_univ.prod hK).image ((hρ.comp continuous_fst).clm_apply
      continuous_snd), fun x hx ξ ↦ ?_⟩
  rw [coefficient_average]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  have hg : (ρ g).symm x ∉ K := fun hxK ↦ hx ⟨(g, (ρ g).symm x), ⟨Set.mem_univ _, hxK⟩, by simp⟩
  simp [hKa _ hg]

end Average

end Symbol

end TauCeti
