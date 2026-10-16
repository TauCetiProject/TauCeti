/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AutomorphismAction
public import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia

/-!
# The decomposition group acts on the completion

Let `L/K` be an extension of number fields, `v` a finite place of `K`, and `w` a finite place of
`L` above `v`. An automorphism `σ ∈ Aut(L/K)` carries `w` to the place `σ • w`, and extends by
continuity to an isomorphism of completions `L_w ≃ₐ[K_v] L_{σ • w}`. This file constructs that
isomorphism, `completionCongr`, and restricts it to the decomposition group, the stabilizer of
`w`, to obtain the homomorphism

```text
decompositionHom v w : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (L_w ≃ₐ[K_v] L_w).
```

When `L/K` is Galois this homomorphism is an isomorphism, `decompositionEquiv`: the
decomposition group of `w` *is* the Galois group of the local extension `L_w/K_v`. Injectivity
is density of `L` in `L_w`; surjectivity is a count. The decomposition group has `e(w ∣ v) ·
f(w ∣ v)` elements, that product is the local degree `[L_w : K_v]`, and a finite extension of
fields has at most `[L_w : K_v]` automorphisms, so the embedding is already onto. The same count
shows that `L_w/K_v` is itself Galois.

The target place of `completionCongr` is an arbitrary `w'` together with the equation
`w'.asIdeal = σ • w.asIdeal`, so that no transport along an equality of places is needed.
Both completions carry the canonical `K_v`-algebra structure of `completionAlgHom`, which is
available in the `AdicCompletionExtension` scope.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.completionCongr`: the isomorphism `L_w ≃ₐ[K_v] L_{w'}`
  induced by `σ` when `w' = σ • w`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom`: the action of the decomposition group
  of `w` on `L_w`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`: that action, as an isomorphism onto
  the local Galois group, when `L/K` is Galois.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_apply_eq_of_asIdeal_eq_smul`: `σ` carries the
  `w`-adic valuation to the `σ • w`-adic valuation.
* `IsDedekindDomain.HeightOneSpectrum.completionCongr_algebraMap` and
  `IsDedekindDomain.HeightOneSpectrum.eq_completionCongr_of_continuous`: `completionCongr`
  extends `σ`, uniquely among continuous ring homomorphisms.
* `IsDedekindDomain.HeightOneSpectrum.valued_completionCongr`: `completionCongr` preserves the
  completion valuations.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_algebraMap`: the defining property
  `decompositionHom v w τ x = τ x` for `x ∈ L`; `decompositionHom_algebraMap_ringOfIntegers` is
  its form on `𝓞 L`, and `valued_decompositionHom` says the action preserves the valuation;
  `restrictNormalHom_restrictScalarsHom_decompositionHom` says that restricting the action back
  to `L` recovers the automorphism.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_injective`: the decomposition group
  embeds into `Aut(L_w/K_v)`.
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_conj`: compatibility with the action of
  `Aut(L/K)` on the places above `v`; conjugating by `σ` corresponds to transporting along
  `completionCongr σ`.
* `IsDedekindDomain.HeightOneSpectrum.stabilizer_eq_bot_of_adjoin_eq_top`: the decomposition
  group is trivial when `L` is generated over `K` by elements whose images in `L_w` come from
  `K_v`; for `L/K` Galois the local degree is then one
  (`IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_eq_one_of_adjoin_eq_top`).
* `IsDedekindDomain.HeightOneSpectrum.decompositionHom_surjective` and
  `IsDedekindDomain.HeightOneSpectrum.decompositionEquiv`: for `L/K` Galois the decomposition
  group of `w` is the Galois group of `L_w/K_v`.
* `IsDedekindDomain.HeightOneSpectrum.isGalois_adicCompletion`: for `L/K` Galois the local
  extension `L_w/K_v` is Galois; and
  `IsDedekindDomain.HeightOneSpectrum.card_algEquiv_adicCompletion`: a locally Galois completion
  has `e(w ∣ v) · f(w ∣ v)` automorphisms.
* `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_fixedField`: for a subgroup `H` of
  `Gal(L/K)`, the local degree of `L ^ H` at the place below `w` is `[D(w) : D(w) ∩ H]`; and
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_fixedField_eq_one_iff`: it is one
  exactly when `D(w) ≤ H`.
* `IsDedekindDomain.HeightOneSpectrum.isCyclic_algEquiv_adicCompletion_of_isUnramifiedAt`: at an
  unramified place the local Galois group is cyclic of order `f(w ∣ v)`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §9.
-/

public section
noncomputable section

open IsDedekindDomain Module NumberField
open scoped NumberField Pointwise AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

/-- An automorphism `σ` of `L/K` carries the `w`-adic valuation to the `w'`-adic valuation
when `w' = σ • w`. -/
theorem valuation_apply_eq_of_asIdeal_eq_smul (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝒪 L)} (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    w'.valuation L (σ x) = w.valuation L x := by
  let e := MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝒪 L) σ
  have hσ : (IsFractionRing.ringEquivOfRingEquiv e : L ≃+* L) = σ.toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝒪 L)) (S := L) (RingHom.ext fun r ↦ ?_)
    simp [e]
  have hw : w'.asIdeal = Ideal.map e w.asIdeal := by
    rw [h, Ideal.pointwise_smul_def]
    -- `e` and `MulSemiringAction.toRingHom _ _ σ` bundle the same map, as an equivalence and as
    -- a homomorphism respectively
    rfl
  rw [← valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hw x, hσ, AlgEquiv.coe_toRingEquiv]

variable [NumberField K] (v : HeightOneSpectrum (𝒪 K))

/-- The isomorphism of completions `L_w ≃ₐ[K_v] L_{w'}` induced by an automorphism `σ` of `L/K`
carrying `w` to `w'`: the continuous extension of `σ`. -/
def completionCongr (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝒪 L)}
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
    (h : w'.asIdeal = σ • w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := adicCompletionCongr w w' σ.toRingEquiv
    (valuation_apply_eq_of_asIdeal_eq_smul σ h)) fun a ↦ by
    -- both sides are continuous in `a` and extend `K → L`, so they are the canonical map
    have := eq_completionAlgHom_of_continuous v w'
      ((adicCompletionCongr w w' σ.toRingEquiv
        (valuation_apply_eq_of_asIdeal_eq_smul σ h)).toRingHom.comp
          (completionAlgHom v w).toRingHom)
      ((continuous_adicCompletionCongr _).comp (continuous_completionAlgHom v w)) fun x ↦ by
        simp [IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    rw [algebraMap_eq_completionAlgHom, algebraMap_eq_completionAlgHom]
    exact congr($this a)

variable {v}

section completionCongr

variable {w w' : HeightOneSpectrum (𝒪 L)} [w.asIdeal.LiesOver v.asIdeal]
  [w'.asIdeal.LiesOver v.asIdeal]

/-- `completionCongr v σ h` extends `σ`. -/
@[simp]
theorem completionCongr_algebraMap (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) (x : L) :
    completionCongr v σ h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) := by
  rw [completionCongr, AlgEquiv.ofRingEquiv_apply, adicCompletionCongr_algebraMap,
    AlgEquiv.coe_toRingEquiv]

variable (v) in
/-- `completionCongr` is continuous. -/
theorem continuous_completionCongr (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) :
    Continuous (completionCongr v σ h) :=
  continuous_adicCompletionCongr _

/-- `completionCongr` is the only continuous ring homomorphism `L_w →+* L_{w'}` extending `σ`. -/
theorem eq_completionCongr_of_continuous (σ : L ≃ₐ[K] L)
    (h : w'.asIdeal = σ • w.asIdeal) {f : w.adicCompletion L →+* w'.adicCompletion L}
    (hf : Continuous f)
    (hfL : ∀ x : L, f (algebraMap L _ x) = algebraMap L (w'.adicCompletion L) (σ x)) :
    f = (completionCongr v σ h).toRingEquiv.toRingHom := by
  apply eq_adicCompletionCongr_of_continuous
  · exact hf
  · exact hfL

/-- `completionCongr` preserves the valuations of the completions. -/
@[simp]
theorem valued_completionCongr (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (completionCongr v σ h x) = Valued.v x :=
  valued_adicCompletionCongr _ x

/-- `completionCongr` depends only on the automorphism, not on the proof that it carries `w`
to `w'`. -/
private theorem completionCongr_congr {σ σ' : L ≃ₐ[K] L} (hσσ' : σ = σ')
    (h : w'.asIdeal = σ • w.asIdeal) (h' : w'.asIdeal = σ' • w.asIdeal) :
    completionCongr v σ h = completionCongr v σ' h' := by
  subst hσσ'
  rfl

/-- `completionCongr` of the identity is the identity. -/
@[simp]
theorem completionCongr_one :
    completionCongr (w := w) (w' := w) v (1 : L ≃ₐ[K] L)
      (by simp) = AlgEquiv.refl :=
  AlgEquiv.toRingEquiv_injective adicCompletionCongr_one

/-- `completionCongr` is multiplicative: transporting along `σ` and then along `τ` is
transporting along `τ * σ`. -/
@[simp]
theorem completionCongr_trans {w'' : HeightOneSpectrum (𝒪 L)} [w''.asIdeal.LiesOver v.asIdeal]
    (σ τ : L ≃ₐ[K] L) (hσ : w'.asIdeal = σ • w.asIdeal) (hτ : w''.asIdeal = τ • w'.asIdeal) :
    (completionCongr v σ hσ).trans (completionCongr v τ hτ) =
      completionCongr v (τ * σ) (by rw [hτ, hσ, mul_smul]) :=
  AlgEquiv.toRingEquiv_injective (adicCompletionCongr_trans _ _ _ _)

/-- The inverse of `completionCongr v σ h` is `completionCongr` of `σ⁻¹`. -/
@[simp]
theorem completionCongr_symm (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal) :
    (completionCongr v σ h).symm =
      completionCongr v σ⁻¹
        (by rw [h, inv_smul_smul]) :=
  AlgEquiv.toRingEquiv_injective (adicCompletionCongr_symm _)

end completionCongr

variable (v) (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The action of the decomposition group of `w` on the completion `L_w`: each element of the
stabilizer of `w` extends by continuity to a `K_v`-algebra automorphism of `L_w`. -/
def decompositionHom :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal →* (w.adicCompletion L ≃ₐ[v.adicCompletion K]
      w.adicCompletion L) where
  toFun τ := completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm
  map_one' := completionCongr_one
  map_mul' σ τ := (completionCongr_trans (τ : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L)
      (MulAction.mem_stabilizer_iff.mp τ.2).symm
      (MulAction.mem_stabilizer_iff.mp σ.2).symm).symm

variable {v w}

/-- An element of the decomposition group acts on `L_w` by `completionCongr`. -/
theorem decompositionHom_apply (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    decompositionHom v w τ =
      completionCongr v (τ : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp τ.2).symm :=
  (rfl)

/-- The defining property of `decompositionHom`: on `L` it is the action of the automorphism. -/
@[simp]
theorem decompositionHom_algebraMap (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : L) :
    decompositionHom v w τ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((τ : L ≃ₐ[K] L) x) := by
  rw [decompositionHom_apply, completionCongr_algebraMap]

/-- Restricting the action of an element of the decomposition group on `L_w` back to `L` recovers
the element: composing `decompositionHom` with restriction `Aut(L_w/K_v) → Aut(L/K)` recovers the
inclusion of the decomposition subgroup into `Aut(L/K)`. -/
@[simp]
theorem restrictNormalHom_restrictScalarsHom_decompositionHom [Normal K L]
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K) (decompositionHom v w τ) =
      τ := by
  ext x
  exact (algebraMap L (w.adicCompletion L)).injective <|
    (AlgEquiv.restrictNormal_commutes ((decompositionHom v w τ).restrictScalars K) L x).trans
      (decompositionHom_algebraMap (v := v) τ x)

/-- On the ring of integers of `L`, `decompositionHom` is the action of the automorphism. -/
theorem decompositionHom_algebraMap_ringOfIntegers
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) (x : 𝒪 L) :
    decompositionHom v w τ (algebraMap (𝒪 L) (w.adicCompletion L) x) =
      algebraMap (𝒪 L) (w.adicCompletion L) ((τ : L ≃ₐ[K] L) • x) := by
  rw [IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L) x,
    IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L) (_ • x),
    decompositionHom_algebraMap, NumberField.algebraMap_smul_eq_apply]

/-- The action of the decomposition group on `L_w` preserves the valuation of `L_w`. -/
@[simp]
theorem valued_decompositionHom (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (decompositionHom v w τ x) = Valued.v x := by
  rw [decompositionHom_apply, valued_completionCongr]

variable (v) in
/-- Each element of the decomposition group acts continuously on `L_w`. -/
theorem continuous_decompositionHom (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    Continuous (decompositionHom v w τ) := by
  rw [decompositionHom_apply]
  exact continuous_completionCongr v _ _

variable (v w) in
/-- The decomposition group of `w` acts faithfully on `L_w`. -/
theorem decompositionHom_injective : Function.Injective (decompositionHom v w) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  ext x
  have := congr($hτ (algebraMap L (w.adicCompletion L) x))
  rw [decompositionHom_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this

/-- **Compatibility of `decompositionHom` with the action on places.** If `σ` carries `w` to
`w'` and `τ` stabilizes `w`, then the action of `σ τ σ⁻¹` on `L_{w'}` is the action of `τ` on
`L_w` transported along `completionCongr σ`. -/
theorem decompositionHom_conj {w' : HeightOneSpectrum (𝒪 L)} [w'.asIdeal.LiesOver v.asIdeal]
    (σ : L ≃ₐ[K] L) (h : w'.asIdeal = σ • w.asIdeal)
    (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    (τ' : MulAction.stabilizer (L ≃ₐ[K] L) w'.asIdeal)
    (hτ : (τ' : L ≃ₐ[K] L) = σ * τ * σ⁻¹) :
    decompositionHom v w' τ' =
      (completionCongr v σ h).symm.trans
        ((decompositionHom v w τ).trans (completionCongr v σ h)) := by
  rw [decompositionHom_apply, decompositionHom_apply, completionCongr_symm, completionCongr_trans,
    completionCongr_trans]
  exact completionCongr_congr (by rw [hτ, mul_assoc]) _ _

/-- An element of the decomposition group of `w` fixes every `x ∈ L` whose image in `L_w` comes
from `K_v`: its action on `L_w` is `K_v`-linear and extends its action on `L`. -/
theorem apply_eq_self_of_algebraMap_mem_range (τ : MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal)
    {x : L} (hx : algebraMap L (w.adicCompletion L) x ∈
      (algebraMap (v.adicCompletion K) (w.adicCompletion L)).range) :
    (τ : L ≃ₐ[K] L) x = x := by
  obtain ⟨c, hc⟩ := hx
  apply (algebraMap L (w.adicCompletion L)).injective
  rw [← decompositionHom_algebraMap (v := v), ← hc, AlgEquiv.commutes]

/-- **The decomposition group is trivial when `L` is generated by elements of `K_v`.** If `L` is
generated over `K` by elements whose images in `L_w` come from `K_v`, then the decomposition group
of `w` is trivial. -/
theorem stabilizer_eq_bot_of_adjoin_eq_top {s : Set L} (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, algebraMap L (w.adicCompletion L) x ∈
      (algebraMap (v.adicCompletion K) (w.adicCompletion L)).range) :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal = ⊥ := by
  rw [eq_bot_iff, ← IntermediateField.fixingSubgroup_top, ← hs, ← IntermediateField.le_iff_le,
    IntermediateField.adjoin_le_iff]
  exact fun x hx τ ↦ apply_eq_self_of_algebraMap_mem_range τ (h x hx)

/-! ### The decomposition group is the local Galois group -/

section IsGalois

variable (v w) [IsGalois K L]

/-- **The decomposition group of `w` has order the local degree.** For `L/K` Galois the
decomposition group of `w` has `e(w ∣ v) · f(w ∣ v)` elements, and that product is the degree
of `L_w` over `K_v`. -/
theorem card_stabilizer_eq_finrank_adicCompletion :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) =
      finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : Finite (𝒪 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  rw [finrank_adicCompletion v w,
    Ideal.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
      (R := 𝒪 K) (G := L ≃ₐ[K] L) w.asIdeal]

/-- **Local degree one.** If the Galois extension `L/K` is generated by elements whose images in
`L_w` come from `K_v`, then `L_w = K_v`: the local degree `[L_w : K_v]` is one. -/
theorem finrank_adicCompletion_eq_one_of_adjoin_eq_top {s : Set L}
    (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, algebraMap L (w.adicCompletion L) x ∈
      (algebraMap (v.adicCompletion K) (w.adicCompletion L)).range) :
    finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  rw [← card_stabilizer_eq_finrank_adicCompletion v w, stabilizer_eq_bot_of_adjoin_eq_top hs h,
    Subgroup.card_bot]

omit [w.asIdeal.LiesOver v.asIdeal] in
/-- **The local degree of a fixed field.** Let `L/K` be Galois, `H` a subgroup of `Gal(L/K)` and
`E = L ^ H`. For a place `u` of `E` between `v` and `w`, the local degree `[E_u : K_v]` is the
index `[D(w) : D(w) ∩ H]` of `D(w) ∩ H` in the decomposition group of `w`. In particular `u` has
local degree one over `v` exactly when `D(w) ≤ H` (`finrank_adicCompletion_fixedField_eq_one_iff`).
-/
theorem finrank_adicCompletion_fixedField (H : Subgroup (L ≃ₐ[K] L))
    (u : HeightOneSpectrum (𝒪 (IntermediateField.fixedField H))) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] :
    finrank (v.adicCompletion K) (u.adicCompletion (IntermediateField.fixedField H)) =
      H.relIndex (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) := by
  have : Finite (𝒪 (IntermediateField.fixedField H) ⧸ u.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient u.ne_bot
  rw [finrank_adicCompletion v u, Ideal.LiesOver.over (P := w.asIdeal) (p := u.asIdeal),
    Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex]

omit [w.asIdeal.LiesOver v.asIdeal] in
/-- **A fixed field has local degree one exactly when its defining subgroup contains the
decomposition group.** Let `L/K` be Galois, `H` a subgroup of `Gal(L/K)` and `E = L ^ H`. For a
place `u` of `E` between `v` and `w`, the local degree `[E_u : K_v]` is one if and only if
`D(w) ≤ H`. -/
theorem finrank_adicCompletion_fixedField_eq_one_iff (H : Subgroup (L ≃ₐ[K] L))
    (u : HeightOneSpectrum (𝒪 (IntermediateField.fixedField H))) [u.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver u.asIdeal] :
    finrank (v.adicCompletion K) (u.adicCompletion (IntermediateField.fixedField H)) = 1 ↔
      MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ≤ H := by
  rw [finrank_adicCompletion_fixedField v w H u, Subgroup.relIndex_eq_one]

/-- **The decomposition group of `w` exhausts `Aut(L_w/K_v)`.** For `L/K` Galois every
`K_v`-algebra automorphism of `L_w` is the continuous extension of an automorphism of `L/K`
stabilizing `w`. -/
-- The decomposition group has `[L_w : K_v]` elements and a finite extension of fields has at
-- most that many automorphisms, so the injection of the previous lemma is already onto.
theorem decompositionHom_surjective : Function.Surjective (decompositionHom v w) := by
  refine ((Nat.bijective_iff_injective_and_card (decompositionHom v w)).mpr
    ⟨decompositionHom_injective v w, le_antisymm ?_ ?_⟩).surjective
  · exact Nat.card_le_card_of_injective _ (decompositionHom_injective v w)
  · rw [card_stabilizer_eq_finrank_adicCompletion v w]
    exact Nat.card_eq_fintype_card.trans_le AlgEquiv.card_le

/-- **The decomposition group of `w` is the Galois group of `L_w/K_v`.** -/
def decompositionEquiv :
    MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal ≃*
      (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  MulEquiv.ofBijective (decompositionHom v w)
    ⟨decompositionHom_injective v w, decompositionHom_surjective v w⟩

@[simp]
theorem coe_decompositionEquiv : ⇑(decompositionEquiv v w) = decompositionHom v w := (rfl)

/-- **A completion of a Galois extension is Galois.** For `L/K` Galois the local extension
`L_w/K_v` at a finite place `w` of `L` is a Galois extension. -/
-- The decomposition group of `w` already supplies `[L_w : K_v]` automorphisms.
theorem isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _
    ((Nat.card_congr (decompositionEquiv v w).toEquiv).symm.trans
      (card_stabilizer_eq_finrank_adicCompletion v w))

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.isGalois_adicCompletion

end IsGalois

section IsGaloisAdicCompletion

variable (v w) [IsGalois (v.adicCompletion K) (w.adicCompletion L)]

/-- **The local Galois group at `w` has order `e(w ∣ v) · f(w ∣ v)`.** -/
theorem card_algEquiv_adicCompletion :
    Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝒪 K) * w.asIdeal.inertiaDeg (𝒪 K) := by
  rw [IsGalois.card_aut_eq_finrank, finrank_adicCompletion v w]

end IsGaloisAdicCompletion

/-! ### The local Galois group at an unramified place -/

section IsUnramifiedAt

variable (v w) [IsGalois (v.adicCompletion K) (w.adicCompletion L)]
  [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal]

/-- **The local Galois group at an unramified place has order `f(w ∣ v)`.** -/
theorem card_algEquiv_adicCompletion_of_isUnramifiedAt :
    Nat.card (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) =
      w.asIdeal.inertiaDeg (𝒪 K) := by
  rw [card_algEquiv_adicCompletion v w, Ideal.ramificationIdx_eq_one w.asIdeal (𝒪 K), one_mul]

end IsUnramifiedAt

section IsGaloisUnramifiedAt

variable (v w) [IsGalois K L] [Algebra.IsUnramifiedAt (𝒪 K) w.asIdeal]

/-- **The local Galois group at an unramified place is cyclic.** -/
-- It is the image of the decomposition group of `w`, which an arithmetic Frobenius generates.
theorem isCyclic_algEquiv_adicCompletion_of_isUnramifiedAt :
    IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L) :=
  have := Ideal.isCyclic_stabilizer_of_isUnramifiedAt (K := K) w.asIdeal w.ne_bot
  isCyclic_of_surjective _ (decompositionHom_surjective v w)

end IsGaloisUnramifiedAt

end IsDedekindDomain.HeightOneSpectrum
