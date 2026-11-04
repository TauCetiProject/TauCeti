/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ULift
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

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
* `TauCeti.signFiberEquiv`: for a double cover, evaluation at a point of the fibre.
* `IsCoveringMap.signLocalSystem`: these modules as a local coefficient system.
* `IsCoveringMap.signLocalSystemObjEquiv`: the fibres of the sign local system are the modules
  `TauCeti.signFiber`.
* `IsCoveringMap.signLocalSystemIsoOfSection`: the trivialization given by a continuous section.

## Main results

* `IsCoveringMap.signLocalSystemObjEquiv_map_apply_monodromy`: transport along a path evaluated
  at the endpoint of a lift is the original function evaluated at its starting point.

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

section DoubleCover

variable {σ : E → E} {hσ : p ∘ σ = p} (hfix : ∀ e, σ e ≠ e)
  (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

include hfix hfib in
private theorem signFiber_bijective_eval {x : X} (e : p ⁻¹' {x}) :
    Function.Bijective fun f : signFiber R σ hσ x ↦ (f : p ⁻¹' {x} → R) e := by
  classical
  have hσe : Function.fiberMap σ hσ x e ≠ e := fun h ↦
    hfix e ((Function.fiberMap_apply_coe σ hσ x e).symm.trans (congrArg Subtype.val h))
  -- Every point of the fibre is `e` or `σ e`.
  have hcases (e' : p ⁻¹' {x}) : e' = e ∨ e' = Function.fiberMap σ hσ x e := by
    rcases hfib e e' (e'.2.trans e.2.symm) with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext (h.trans (Function.fiberMap_apply_coe σ hσ x e).symm))
  refine ⟨fun f g hfg ↦ Subtype.ext (funext fun e' ↦ ?_), fun r ↦ ?_⟩
  · rcases hcases e' with rfl | rfl
    · exact hfg
    · rw [mem_signFiber_iff.1 f.2, mem_signFiber_iff.1 g.2]
      exact congrArg Neg.neg hfg
  · refine ⟨⟨fun e' ↦ if e' = e then r else -r, mem_signFiber_iff.2 fun e' ↦ ?_⟩, ?_⟩
    · rcases hcases e' with rfl | rfl
      · simp [hσe]
      · -- `σ (σ e)` lies over `x`, and it is not `σ e`, since `σ` has no fixed points.
        have hσσ : Function.fiberMap σ hσ x (Function.fiberMap σ hσ x e) = e := by
          rcases hcases (Function.fiberMap σ hσ x (Function.fiberMap σ hσ x e)) with h | h
          · exact h
          · exact absurd (congrArg Subtype.val h) (by
              simpa only [Function.fiberMap_apply_coe] using hfix _)
        simp [hσσ, hσe]
    · simp

/-- When the fibres of `p` are the pairs `{e, σ e}` with `σ e ≠ e`, evaluation at a point `e` of
the fibre over `x` identifies the functions changing sign under `σ` with `R`. -/
def signFiberEquiv {x : X} (e : p ⁻¹' {x}) : signFiber R σ hσ x ≃ₗ[R] R :=
  LinearEquiv.ofBijective ((LinearMap.proj e).comp (signFiber R σ hσ x).subtype)
    (signFiber_bijective_eval hfix hfib e)

@[simp]
theorem signFiberEquiv_apply {x : X} (e : p ⁻¹' {x}) (f : signFiber R σ hσ x) :
    signFiberEquiv hfix hfib e f = (f : p ⁻¹' {x} → R) e :=
  (rfl)

/-- Evaluation at the other point of the fibre is the negative of evaluation at `e`. It has high
priority so that `simp` applies it before unfolding the evaluation by `signFiberEquiv_apply`. -/
@[simp high]
theorem signFiberEquiv_fiberMap {x : X} (e : p ⁻¹' {x}) (f : signFiber R σ hσ x) :
    signFiberEquiv hfix hfib (Function.fiberMap σ hσ x e) f = -signFiberEquiv hfix hfib e f := by
  simp [mem_signFiber_iff.1 f.2]

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
  rw [mem_signFiber_iff.1 ((signFiberEquiv (hσ := hσ) hfix hfib e).symm r).2,
    signFiberEquiv_symm_apply_self]

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
    exact congrArg f.1 (congrFun hp.monodromy_refl e)
  map_comp {x y z} γ δ := by
    ext f e
    simp only [IsIso.inv_comp]
    exact congrArg f.1 (hp.monodromy_trans_apply (inv δ) (inv γ) e)

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
      exact congrArg f.1 (hp.monodromy_section s.continuous hs (inv γ))

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

end IsCoveringMap
