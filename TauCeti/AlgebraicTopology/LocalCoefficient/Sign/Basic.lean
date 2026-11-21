/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality
import TauCeti.LinearAlgebra.Pi.SignChange

/-!
# The sign local system of a covering with an involution

Let `p : E → X` be a covering map and `σ : E → E` a continuous map over `X`, typically the deck
involution of a double cover. Over each point `x` consider the `R`-module of functions `f` on the
fibre `p ⁻¹' {x}` that change sign under `σ`, that is `f (σ e) = -f e`
(`TauCeti.signFiber`). Monodromy commutes with `σ`, so precomposition with monodromy along the
inverse path transports these modules along path classes, and they form a local coefficient system
(`IsCoveringMap.signLocalSystem`), whose fibres are identified with these modules by
`IsCoveringMap.signLocalSystemObjEquiv`.

When the fibres of `p` are the pairs `{e, σ e}` with `σ e ≠ e`, evaluation at either point of a
fibre identifies its sign module with `R` (`TauCeti.signFiberEquiv`), and evaluation at the other
point gives the negative of that identification. Transport along a path sends evaluation at a
point to evaluation at the endpoint of its lift
(`IsCoveringMap.signLocalSystemObjEquiv_map_apply_monodromy`). Monodromy follows continuous
sections (`IsCoveringMap.monodromy_section`), so a continuous section of such a double cover
trivializes the sign local system (`IsCoveringMap.signLocalSystemIsoOfSection`).

For the orientation double cover of a real vector bundle `E` with integral coefficients this is
the orientation local system `o(E)`: its fibre over `b` is a copy of `ℤ` whose two generators are
the two orientations of `E_b`, and an orientation of the bundle trivializes it.

## Main definitions

* `TauCeti.signFiber`: the functions on a fibre that change sign under `σ`.
* `TauCeti.antisymmetrize`: for an involution `σ`, the map sending a formal sum `f` of points of a
  fibre to the function `e ↦ f e - f (σ e)`.
* `TauCeti.signFiberEquiv`: for a double cover, evaluation at a point of the fibre.
* `IsCoveringMap.signLocalSystem`: these modules as a local coefficient system.
* `IsCoveringMap.signLocalSystemObjEquiv`: the fibres of the sign local system are the modules
  `TauCeti.signFiber`.
* `IsCoveringMap.signLocalSystemIsoOfSection`: the trivialization given by a continuous section.

## Main results

* `TauCeti.sum_eq_zero_of_mem_signFiber` and `TauCeti.mem_signFiber_of_sum_eq_zero`: for a double
  cover, the functions on a finite fibre changing sign under `σ` are those whose values sum to zero.
* `IsCoveringMap.signLocalSystemObjEquiv_map_apply_monodromy`: transport along a path evaluated
  at the endpoint of a lift is the original function evaluated at its starting point.
* `IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one` and
  `IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_neg_one`: for a double cover, a loop
  acts by `1` when its lift starting at `e` closes up and by `-1` when that lift ends at `σ e`;
  every loop does one or the other
  (`IsCoveringMap.monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficient systems as functors out of the
  fundamental groupoid, and the orientation system of a manifold).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover of a vector bundle).
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti

variable (R : Type u) [Ring R] {E : Type w} {X : Type*} {p : E → X}

/-- The functions on the fibre of `p` over `x` that change sign under the map `σ` over `X`:
those `f` with `f (σ e) = -f e`. It is the kernel of `f ↦ f ∘ σ + f`. -/
def signFiber (σ : E → E) (hσ : p ∘ σ = p) (x : X) : Submodule R (p ⁻¹' {x} → R) :=
  LinearMap.ker (LinearMap.funLeft R R (Function.fiberMap σ hσ x) + LinearMap.id)

variable {R}

@[simp]
theorem mem_signFiber_iff {σ : E → E} {hσ : p ∘ σ = p} {x : X} {f : p ⁻¹' {x} → R} :
    f ∈ signFiber R σ hσ x ↔ ∀ e, f (Function.fiberMap σ hσ x e) = -f e := by
  simp only [signFiber, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, funext_iff,
    LinearMap.funLeft_apply, Pi.neg_apply, add_eq_zero_iff_eq_neg]

variable (R) in
/-- Antisymmetrization on the fibre of `p` over `x` for an involution `σ` over `X`: a formal sum
`f` of points of the fibre goes to the function `e ↦ f e - f (σ e)`, which changes sign under
`σ`. -/
def antisymmetrize {σ : E → E} (hσ : p ∘ σ = p) (hσσ : Function.Involutive σ) (x : X) :
    ((p ⁻¹' {x}) →₀ R) →ₗ[R] signFiber R σ hσ x :=
  LinearMap.codRestrict (signFiber R σ hσ x)
    ((LinearMap.id - LinearMap.funLeft R R (Function.fiberMap σ hσ x)) ∘ₗ Finsupp.lcoeFun)
    fun f ↦ mem_signFiber_iff.2 fun e ↦ by
      simp [Function.fiberMap_fiberMap_of_involutive hσσ hσ]

/-- Antisymmetrization evaluated at a point `e` of the fibre is `f e - f (σ e)`. -/
@[simp]
theorem coe_antisymmetrize_apply {σ : E → E} (hσ : p ∘ σ = p) (hσσ : Function.Involutive σ)
    (x : X) (f : (p ⁻¹' {x}) →₀ R) (e : p ⁻¹' {x}) :
    (antisymmetrize R hσ hσσ x f : p ⁻¹' {x} → R) e = f e - f (Function.fiberMap σ hσ x e) :=
  (rfl)

section DoubleCover

variable {σ : E → E} {hσ : p ∘ σ = p} (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib in
private theorem signFiber_eval_bijective {x : X} (e : p ⁻¹' {x}) :
    Function.Bijective fun f : signFiber R σ hσ x ↦ (f : p ⁻¹' {x} → R) e := by
  refine eval_bijective_of_mem_iff_apply_eq_neg (σ := Function.fiberMap σ hσ x)
    (fun e' h ↦ hfix e'
      ((Function.fiberMap_apply_coe σ hσ x e').symm.trans (congrArg Subtype.val h)))
    (fun e' ↦ ?_) fun _ ↦ mem_signFiber_iff
  -- Every point of the fibre is `e` or `σ e`.
  rcases hfib e e' (e'.property.trans e.property.symm) with h | h
  · exact .inl (Subtype.ext h)
  · exact .inr (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm))

/-- When the fibres of `p` are the pairs `{e, σ e}` with `σ e ≠ e`, evaluation at a point `e` of
the fibre over `x` identifies the functions changing sign under `σ` with `R`. -/
def signFiberEquiv {x : X} (e : p ⁻¹' {x}) : signFiber R σ hσ x ≃ₗ[R] R :=
  LinearEquiv.ofBijective ((LinearMap.proj e).comp (signFiber R σ hσ x).subtype)
    (signFiber_eval_bijective hfix hfib e)

@[simp]
theorem signFiberEquiv_apply {x : X} (e : p ⁻¹' {x}) (f : signFiber R σ hσ x) :
    signFiberEquiv hfix hfib e f = (f : p ⁻¹' {x} → R) e :=
  (rfl)

/-- Evaluation at the other point of the fibre is the negative of evaluation at `e`. It has high
priority so that `simp` applies it before unfolding the evaluation by `signFiberEquiv_apply`. -/
@[simp high]
theorem signFiberEquiv_fiberMap {x : X} (e : p ⁻¹' {x}) (f : signFiber R σ hσ x) :
    signFiberEquiv hfix hfib (Function.fiberMap σ hσ x e) f = -signFiberEquiv hfix hfib e f := by
  simp [mem_signFiber_iff.1 f.property]

/-- The function changing sign under `σ` with value `r` at `e`, evaluated at `e`. -/
@[simp]
theorem signFiberEquiv_symm_apply_self {x : X} (e : p ⁻¹' {x}) (r : R) :
    ((signFiberEquiv (hσ := hσ) hfix hfib e).symm r : p ⁻¹' {x} → R) e = r :=
  (signFiberEquiv_apply hfix hfib e _).symm.trans (LinearEquiv.apply_symm_apply _ r)

/-- The function changing sign under `σ` with value `r` at `e`, evaluated at the other point of
the fibre. -/
@[simp]
theorem signFiberEquiv_symm_apply_fiberMap {x : X} (e : p ⁻¹' {x}) (r : R) :
    ((signFiberEquiv (hσ := hσ) hfix hfib e).symm r : p ⁻¹' {x} → R)
      (Function.fiberMap σ hσ x e) = -r := by
  rw [mem_signFiber_iff.1 ((signFiberEquiv (hσ := hσ) hfix hfib e).symm r).property,
    signFiberEquiv_symm_apply_self]

include hfix in
/-- The values of a function changing sign under a fixed-point-free involution sum to zero over
a finite fibre. -/
theorem sum_eq_zero_of_mem_signFiber (hσσ : Function.Involutive σ) {x : X}
    [Fintype (p ⁻¹' {x})] {g : p ⁻¹' {x} → R} (hg : g ∈ signFiber R σ hσ x) : ∑ e, g e = 0 :=
  Finset.sum_involution (fun e _ ↦ Function.fiberMap σ hσ x e)
    (fun e _ ↦ by rw [mem_signFiber_iff.1 hg, add_neg_cancel])
    (fun e _ _ ↦ Function.fiberMap_ne_self hfix hσ x e)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun e _ ↦ Function.fiberMap_fiberMap_of_involutive hσσ hσ x e)

include hfix hfib in
/-- When every fibre of `p` is a pair `{e, σ e}` with `σ e ≠ e`, a function on a finite fibre whose
values sum to zero changes sign under `σ`. -/
theorem mem_signFiber_of_sum_eq_zero {x : X} [Fintype (p ⁻¹' {x})] {g : p ⁻¹' {x} → R}
    (hg : ∑ e, g e = 0) : g ∈ signFiber R σ hσ x := by
  classical
  refine mem_signFiber_iff.2 fun e ↦ ?_
  have huniv : (Finset.univ : Finset (p ⁻¹' {x})) = {e, Function.fiberMap σ hσ x e} := by
    ext e'
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hfib e e' (e'.property.trans e.property.symm) with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm))
  rw [huniv, Finset.sum_pair (Function.fiberMap_ne_self hfix hσ x e).symm] at hg
  exact eq_neg_of_add_eq_zero_right hg

end DoubleCover

end TauCeti

namespace IsCoveringMap

variable {E : Type w} [TopologicalSpace E] {X : TopCat.{v}} {p : E → X}

variable (R : Type u) [Ring R]

/-- The sign local system of a covering `p` with a continuous map `σ` over the base: its fibre over
`x` is the module `TauCeti.signFiber` of functions on the fibre of `p` that change sign under `σ`
(`IsCoveringMap.signLocalSystemObjEquiv`), and a path class transports such a function by
precomposition with monodromy along the inverse path. For the deck involution of a double cover,
each fibre is a copy of `R` (`TauCeti.signFiberEquiv`). -/
def signLocalSystem (hp : IsCoveringMap p) (σ : C(E, E)) (hσ : p ∘ σ = p) :
    TauCeti.LocalCoefficientSystem.{u, v, max w u} R X where
  obj x := ModuleCat.of R (TauCeti.signFiber R σ hσ x.as)
  map {x y} γ := ModuleCat.ofHom <|
    (LinearMap.funLeft R R (hp.monodromy (inv γ))).restrict fun f hf ↦
      TauCeti.mem_signFiber_iff.2 fun e ↦ by
        simp only [LinearMap.funLeft_apply, ← hp.fiberMap_monodromy hp σ hσ (inv γ) e]
        exact TauCeti.mem_signFiber_iff.1 hf _
  map_id x := by
    ext f e
    simp only [IsIso.inv_id]
    exact congrArg f.val (congrFun hp.monodromy_refl e)
  map_comp {x y z} γ δ := by
    ext f e
    simp only [IsIso.inv_comp]
    exact congrArg f.val (hp.monodromy_trans_apply (inv δ) (inv γ) e)

variable {R} (hp : IsCoveringMap p) (σ : C(E, E)) (hσ : p ∘ σ = p)

/-- The fibre of the sign local system over `x` is the module of functions on the fibre of `p`
changing sign under `σ`. -/
def signLocalSystemObjEquiv (x : FundamentalGroupoid X) :
    (hp.signLocalSystem R σ hσ).obj x ≃ₗ[R] TauCeti.signFiber R σ hσ x.as :=
  LinearEquiv.refl R _

/-- Transport in the sign local system precomposes with monodromy along the inverse path. -/
@[simp]
theorem signLocalSystemObjEquiv_map_apply {x y : FundamentalGroupoid X} (γ : x ⟶ y)
    (f : (hp.signLocalSystem R σ hσ).obj x) (e : p ⁻¹' {y.as}) :
    (hp.signLocalSystemObjEquiv σ hσ y (((hp.signLocalSystem R σ hσ).map γ).hom f) :
      p ⁻¹' {y.as} → R) e =
      (hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) (hp.monodromy (inv γ) e) :=
  (rfl)

/-- Transport along a path, evaluated at the endpoint of the lift starting at `e`, is the
original function evaluated at `e`. -/
theorem signLocalSystemObjEquiv_map_apply_monodromy {x y : FundamentalGroupoid X} (γ : x ⟶ y)
    (f : (hp.signLocalSystem R σ hσ).obj x) (e : p ⁻¹' {x.as}) :
    (hp.signLocalSystemObjEquiv σ hσ y (((hp.signLocalSystem R σ hσ).map γ).hom f) :
      p ⁻¹' {y.as} → R) (hp.monodromy γ e) =
      (hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) e := by
  rw [signLocalSystemObjEquiv_map_apply, ← hp.monodromy_trans_apply γ (inv γ) e]
  have h := congrArg (fun a ↦ hp.monodromy a e) (IsIso.hom_inv_id γ)
  exact congrArg _ (h.trans (congrFun hp.monodromy_refl e))

section DoubleCover

variable {σ hσ} (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)
  (s : C(X, E)) (hs : ∀ x, s x ∈ p ⁻¹' {x})

/-- A continuous section `s` of a double cover whose sheets are exchanged by `σ` trivializes the
sign local system: over `x`, the isomorphism with the constant system evaluates at `s x`. -/
def signLocalSystemIsoOfSection :
    hp.signLocalSystem R σ hσ ≅
      (TauCeti.LocalCoefficientSystem.constantFunctor X).obj (ModuleCat.of R (ULift.{w} R)) :=
  NatIso.ofComponents
    (fun x ↦ (hp.signLocalSystemObjEquiv σ hσ x ≪≫ₗ
      TauCeti.signFiberEquiv hfix hfib ⟨s x.as, hs x.as⟩ ≪≫ₗ ULift.moduleEquiv.symm).toModuleIso)
    -- Both sides evaluate `f` at a point of the fibre over `x`, by definition of the transport
    -- and of `TauCeti.signFiberEquiv`; monodromy along `inv γ` carries `s y.as` to `s x.as`.
    fun {x y} γ ↦ ModuleCat.hom_ext <| LinearMap.ext fun f ↦ ULift.ext <| by
      exact congrArg f.val (hp.monodromy_section s.continuous hs (inv γ))

@[simp]
theorem signLocalSystemIsoOfSection_hom_app_apply (x : FundamentalGroupoid X)
    (f : (hp.signLocalSystem R σ hσ).obj x) :
    (ModuleCat.Hom.hom (B := ModuleCat.of R (ULift.{w} R))
        ((hp.signLocalSystemIsoOfSection hfix hfib s hs).hom.app x)) f =
      ULift.up ((hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) ⟨s x.as, hs x.as⟩) :=
  (rfl)

/-- The inverse of the trivialization sends `r` to the function changing sign under `σ` with value
`r` at `s x`. -/
@[simp]
theorem signLocalSystemIsoOfSection_inv_app_apply (x : FundamentalGroupoid X) (r : R) :
    (hp.signLocalSystemObjEquiv σ hσ x
        (ModuleCat.Hom.hom (A := ModuleCat.of R (ULift.{w} R))
          ((hp.signLocalSystemIsoOfSection hfix hfib s hs).inv.app x) (ULift.up r)) :
        p ⁻¹' {x.as} → R) ⟨s x.as, hs x.as⟩ = r :=
  TauCeti.signFiberEquiv_symm_apply_self hfix hfib _ r

/-- The inverse of the trivialization sends `r` to a function whose value at the other point of
the fibre over `x` is `-r`. -/
@[simp]
theorem signLocalSystemIsoOfSection_inv_app_apply_fiberMap (x : FundamentalGroupoid X) (r : R) :
    (hp.signLocalSystemObjEquiv σ hσ x
        (ModuleCat.Hom.hom (A := ModuleCat.of R (ULift.{w} R))
          ((hp.signLocalSystemIsoOfSection hfix hfib s hs).inv.app x) (ULift.up r)) :
        p ⁻¹' {x.as} → R) (Function.fiberMap σ hσ x.as ⟨s x.as, hs x.as⟩) = -r :=
  TauCeti.signFiberEquiv_symm_apply_fiberMap hfix hfib _ r

end DoubleCover

/-! ### Monodromy of the sign local system of a double cover -/

section Monodromy

open TauCeti.LocalCoefficientSystem (monodromyRepresentation)

variable {σ hσ} (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib

/-- A loop at `x` whose lift starting at `e` closes up acts trivially on the sign local system of a
double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_one {x : X} {g : FundamentalGroup X x}
    {e : p ⁻¹' {x}} (he : hp.monodromy g.asHom e = e) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = 1 := by
  ext f
  apply ((hp.signLocalSystemObjEquiv σ hσ _).trans (TauCeti.signFiberEquiv hfix hfib e)).injective
  simpa [he] using hp.signLocalSystemObjEquiv_map_apply_monodromy σ hσ g.asHom f e

/-- A loop at `x` whose lift starting at `e` ends at `σ e` acts by `-1` on the sign local system of
a double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_neg_one {x : X} {g : FundamentalGroup X x}
    {e : p ⁻¹' {x}} (he : hp.monodromy g.asHom e = Function.fiberMap σ hσ x e) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = -1 := by
  ext f
  apply ((hp.signLocalSystemObjEquiv σ hσ _).trans (TauCeti.signFiberEquiv hfix hfib e)).injective
  have h := hp.signLocalSystemObjEquiv_map_apply_monodromy σ hσ g.asHom f e
  -- The value at `σ e` of a function changing sign under `σ` is minus its value at `e`.
  rw [he, TauCeti.mem_signFiber_iff.1 (hp.signLocalSystemObjEquiv σ hσ _ _).property] at h
  simpa [neg_eq_iff_eq_neg] using h

/-- Every loop at `x` acts by `1` or by `-1` on the sign local system of a double cover. -/
theorem monodromyRepresentation_signLocalSystem_eq_one_or_eq_neg_one {x : X}
    (g : FundamentalGroup X x) :
    monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = 1 ∨
      monodromyRepresentation (hp.signLocalSystem R σ hσ) x g = -1 := by
  rcases isEmpty_or_nonempty (p ⁻¹' {x}) with hx | ⟨⟨e⟩⟩
  · -- Over an empty fibre the sign module is zero.
    refine .inl (LinearMap.ext fun f ↦ (hp.signLocalSystemObjEquiv σ hσ _).injective
      (Subtype.ext (funext fun e ↦ (IsEmpty.false e).elim)))
  rcases hfib e (hp.monodromy g.asHom e) ((hp.monodromy g.asHom e).property.trans e.property.symm)
      with h | h
  · exact .inl (hp.monodromyRepresentation_signLocalSystem_eq_one hfix hfib (Subtype.ext h))
  · exact .inr (hp.monodromyRepresentation_signLocalSystem_eq_neg_one hfix hfib
      (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm)))

end Monodromy

end IsCoveringMap
