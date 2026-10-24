/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import TauCeti.Analysis.Complex.RiemannSurface.SphereMap
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Order.Filter.Germ.Basic
import TauCeti.Analysis.Complex.RiemannSurface.LocalNormalForm
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# The field of meromorphic functions on a connected Riemann surface

A meromorphic function on a Riemann surface `X` is a holomorphic map `f : X → OnePoint ℂ` to the
Riemann sphere which is not the constant map `∞`
(`TauCeti.RiemannSurface.MeromorphicFunction X`). This file makes these functions a field when `X`
is connected, and a `ℂ`-algebra through the constant functions.

The operations are not defined pointwise, since a sum or product of two maps to the sphere has no
meaning at the common poles. Instead, `f` is read in the affine chart of the sphere as a function
`f.finitePart : X → ℂ`, which agrees with `f` away from the poles and is meromorphic in the sense of
`TauCeti.RiemannSurface.MeromorphicAt` at every point
(`TauCeti.RiemannSurface.MeromorphicFunction.meromorphicAt_finitePart`). The pointwise sum of two
finite parts is again meromorphic, and `TauCeti.RiemannSurface.sphereMap` turns it back into a
holomorphic map to the sphere, filling in the removable singularities and poles. This defines
`f + g`, and likewise `f * g`, `-f`, `f - g` and `f⁻¹`.

Each operation is characterized by its values off the poles: for instance `f + g` is the unique
meromorphic function whose value at every point where `f` and `g` are finite is the sum of their
values (`TauCeti.RiemannSurface.MeromorphicFunction.eq_add_iff`). By continuity, a meromorphic
function is determined by its values on the punctured neighbourhoods of the points
(`TauCeti.RiemannSurface.MeromorphicFunction.eq_of_eventually_apply_eq`), and by the identity
theorem the poles of a meromorphic function on a connected Riemann surface are isolated
(`TauCeti.RiemannSurface.MeromorphicFunction.eventually_ne_infty`), so the points where `f` and `g`
are finite fill a punctured neighbourhood of every point. In the same way a meromorphic function
on a connected Riemann surface is determined by the germs of its finite part on these punctured
neighbourhoods. The meromorphic functions therefore embed into a commutative ring compatibly with
the operations, which gives the commutative ring structure. The zeros of a nonzero meromorphic
function are isolated as well, so its finite part is eventually nonzero on every punctured
neighbourhood and its inverse is a multiplicative inverse.

## Main definitions

* `TauCeti.RiemannSurface.MeromorphicFunction X`: the meromorphic functions on `X`, as holomorphic
  maps to the Riemann sphere which are not identically `∞`.
* `TauCeti.RiemannSurface.MeromorphicFunction.finitePart`: a meromorphic function read in the
  affine chart of the sphere, with value `0` at the poles.
* `TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic`: the meromorphic function defined by
  a function `X → ℂ` meromorphic at every point.
* `TauCeti.RiemannSurface.MeromorphicFunction.instField` and
  `TauCeti.RiemannSurface.MeromorphicFunction.instAlgebra`: the field and `ℂ`-algebra structures
  on a connected Riemann surface.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.sphereMap_finitePart`: a meromorphic function is
  recovered from its finite part by `TauCeti.RiemannSurface.sphereMap`.
* `TauCeti.RiemannSurface.MeromorphicFunction.eq_add_iff`,
  `TauCeti.RiemannSurface.MeromorphicFunction.eq_mul_iff`,
  `TauCeti.RiemannSurface.MeromorphicFunction.eq_neg_iff` and
  `TauCeti.RiemannSurface.MeromorphicFunction.eq_inv_iff`: the defining properties of the
  operations.
* `TauCeti.RiemannSurface.MeromorphicFunction.inv_apply_of_eq_infty`: the inverse of a meromorphic
  function vanishes at its poles.
* `TauCeti.RiemannSurface.MeromorphicFunction.finite_setOf_eq_infty` and
  `TauCeti.RiemannSurface.MeromorphicFunction.finite_setOf_eq_zero`: on a compact connected Riemann
  surface, a meromorphic function has finitely many poles, and a nonzero one finitely many zeros.
* `TauCeti.RiemannSurface.MeromorphicFunction.exists_algebraMap_eq_of_forall_ne_infty`: the maximum
  principle, a meromorphic function without poles on a compact connected Riemann surface is
  constant.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1, 1.12 to 1.16.
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Proposition 1.23.
-/

public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A **meromorphic function** on a Riemann surface `X`: a holomorphic map `X → OnePoint ℂ` to the
Riemann sphere which is not the constant map `∞`. On a connected `X` these form a field
(`TauCeti.RiemannSurface.MeromorphicFunction.instField`). -/
structure MeromorphicFunction where
  /-- The underlying map to the Riemann sphere. -/
  toFun : X → OnePoint ℂ
  mdifferentiable' : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  ne_infty' : toFun ≠ fun _ ↦ ∞

namespace MeromorphicFunction

variable {X}

instance : FunLike (MeromorphicFunction X) X (OnePoint ℂ) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

variable {f g : MeromorphicFunction X} {x : X}

@[simp]
theorem coe_mk (f : X → OnePoint ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (h : f ≠ fun _ ↦ ∞) :
    ⇑(⟨f, hf, h⟩ : MeromorphicFunction X) = f :=
  (rfl)

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- A meromorphic function is a holomorphic map to the Riemann sphere. -/
theorem mdifferentiable (f : MeromorphicFunction X) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  f.mdifferentiable'

/-- A meromorphic function is not the constant map `∞`. -/
theorem coe_ne_infty (f : MeromorphicFunction X) : ⇑f ≠ fun _ ↦ ∞ :=
  f.ne_infty'

theorem continuous (f : MeromorphicFunction X) : Continuous f :=
  f.mdifferentiable.continuous

/-! ### The finite part -/

/-- A meromorphic function read in the affine chart of the Riemann sphere: its value at `x` is
`f x` when this is finite, and `0` at a pole of `f`. -/
def finitePart (f : MeromorphicFunction X) (x : X) : ℂ :=
  affineChart (f x)

theorem finitePart_def (f : MeromorphicFunction X) (x : X) :
    f.finitePart x = affineChart (f x) :=
  (rfl)

theorem finitePart_of_eq_coe {z : ℂ} (h : f x = z) : f.finitePart x = z := by
  simp [finitePart, h]

theorem finitePart_of_eq_infty (h : f x = ∞) : f.finitePart x = 0 := by
  simp [finitePart, h]

/-- Away from the poles, a meromorphic function is its finite part. -/
theorem coe_finitePart (h : f x ≠ ∞) : (f.finitePart x : OnePoint ℂ) = f x := by
  obtain ⟨z, hz⟩ := ne_infty_iff_exists.1 h
  rw [finitePart_of_eq_coe hz.symm, hz]

theorem continuousAt_finitePart (h : f x ≠ ∞) : ContinuousAt f.finitePart x :=
  (affineChart.continuousAt (by simpa using h)).comp f.continuous.continuousAt

/-- The value of a meromorphic function at `x` is the limit at `x`, along the punctured
neighbourhoods of `x`, of any map to the sphere that agrees with it near `x`. -/
theorem apply_eq_of_tendsto {φ : X → OnePoint ℂ} {c : OnePoint ℂ} (hφ : Tendsto φ (𝓝[≠] x) (𝓝 c))
    (h : ∀ᶠ y in 𝓝[≠] x, f y = φ y) : f x = c := by
  have := (chartAt ℂ x).nhdsNE_neBot (mem_chart_source ℂ x)
  exact tendsto_nhds_unique_of_eventuallyEq (f.continuous.continuousAt.mono_left
    nhdsWithin_le_nhds) hφ h

/-- **Uniqueness of meromorphic functions.** Two meromorphic functions which agree on a punctured
neighbourhood of every point are equal. -/
theorem eq_of_eventually_apply_eq (h : ∀ x, ∀ᶠ y in 𝓝[≠] x, f y = g y) : f = g :=
  ext fun x ↦ apply_eq_of_tendsto (g.continuous.continuousAt.mono_left nhdsWithin_le_nhds) (h x)

/-- To show that `f` equals `g`, it suffices to compare their values at the points satisfying a
property `p` which holds on a punctured neighbourhood of every point, such as being a pole of
neither of two given meromorphic functions. -/
theorem eq_of_forall_apply_eq {p : X → Prop} (hp : ∀ x, ∀ᶠ y in 𝓝[≠] x, p y)
    (h : ∀ x, p x → f x = g x) : f = g :=
  eq_of_eventually_apply_eq fun x ↦ (hp x).mono h

variable [IsManifold 𝓘(ℂ) 1 X]

/-- The finite part of a meromorphic function is meromorphic at every point. Away from the poles
it is holomorphic; near a pole it is the reciprocal of the holomorphic function reading `f` in the
inverted chart of the sphere. -/
theorem meromorphicAt_finitePart (f : MeromorphicFunction X) (x : X) :
    MeromorphicAt f.finitePart x := by
  have hmd {e : OpenPartialHomeomorph (OnePoint ℂ) ℂ} (he : e ∈ atlas ℂ (OnePoint ℂ))
      (hx : f x ∈ e.source) : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (e ∘ f) y := by
    filter_upwards [f.continuous.continuousAt.eventually (e.open_source.mem_nhds hx)] with y hy
    exact (mdifferentiableAt_atlas he hy).comp y (f.mdifferentiable y)
  rcases eq_or_ne (f x) ∞ with hx | hx
  · have hinv : f.finitePart = (invChart ∘ f)⁻¹ := funext fun y ↦ (inv_invChart (f y)).symm
    rw [hinv]
    exact (meromorphicAt_of_eventually_mdifferentiableAt
      (hmd (Or.inr rfl) (by simp [invChart_source, hx]))).inv
  · exact meromorphicAt_of_eventually_mdifferentiableAt (hmd (Or.inl rfl) (by simpa using hx))

/-! ### Isolated poles -/

section Preconnected

variable [PreconnectedSpace X]

/-- **The poles of a meromorphic function are isolated.** On a connected Riemann surface, a
meromorphic function is finite at every point of a punctured neighbourhood of any point. -/
theorem eventually_ne_infty (f : MeromorphicFunction X) (x : X) : ∀ᶠ y in 𝓝[≠] x, f y ≠ ∞ :=
  eventually_apply_ne_of_ne_const f.mdifferentiable f.coe_ne_infty x

/-- On a connected Riemann surface, a meromorphic function is recovered from its finite part by
taking limits on punctured neighbourhoods. -/
@[simp]
theorem sphereMap_finitePart (f : MeromorphicFunction X) : sphereMap f.finitePart = f :=
  funext fun x ↦ sphereMap_eq_of_eventuallyEq
    ((f.eventually_ne_infty x).mono fun _ ↦ coe_finitePart) f.continuous.continuousAt

/-- On a connected Riemann surface, two meromorphic functions whose finite parts agree on a
punctured neighbourhood of every point are equal. -/
theorem eq_of_eventuallyEq_finitePart (h : ∀ x, f.finitePart =ᶠ[𝓝[≠] x] g.finitePart) :
    f = g := by
  refine eq_of_eventually_apply_eq fun x ↦ ?_
  filter_upwards [h x, f.eventually_ne_infty x, g.eventually_ne_infty x] with y hy hf hg
  rw [← coe_finitePart hf, ← coe_finitePart hg, hy]

end Preconnected

/-! ### Meromorphic functions from functions `X → ℂ` -/

section OfMeromorphic

variable [Nonempty X] {h : X → ℂ} (hh : ∀ x, MeromorphicAt h x)

/-- The meromorphic function on a nonempty Riemann surface defined by a function `h : X → ℂ`
meromorphic at every point: the holomorphic map `TauCeti.RiemannSurface.sphereMap h` to the Riemann
sphere, which agrees with `h` on a punctured neighbourhood of every point. -/
def ofMeromorphic : MeromorphicFunction X where
  toFun := sphereMap h
  mdifferentiable' := mdifferentiable_sphereMap hh
  ne_infty' heq := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have := (chartAt ℂ x).nhdsNE_neBot (mem_chart_source ℂ x)
    obtain ⟨y, hy⟩ := (eventually_sphereMap_eq (hh x)).exists
    exact OnePoint.coe_ne_infty (h y) (hy.symm.trans (congrFun heq y))

@[simp]
theorem coe_ofMeromorphic : ⇑(ofMeromorphic hh) = sphereMap h :=
  (rfl)

/-- The finite part of `TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic hh` agrees with
`h` on a punctured neighbourhood of every point. -/
theorem finitePart_ofMeromorphic_eventuallyEq (x : X) :
    (ofMeromorphic hh).finitePart =ᶠ[𝓝[≠] x] h :=
  (eventually_sphereMap_eq (hh x)).mono fun _ hy ↦ finitePart_of_eq_coe (by rwa [coe_ofMeromorphic])

/-- At a point where `h` is continuous,
`TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic hh` takes the value of `h`. -/
theorem ofMeromorphic_apply_of_continuousAt (hc : ContinuousAt h x) :
    ofMeromorphic hh x = h x :=
  sphereMap_of_continuousAt hc

/-- `TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic hh` depends only on the values of `h`
on a punctured neighbourhood of every point. -/
theorem ofMeromorphic_congr {k : X → ℂ} (hk : ∀ x, MeromorphicAt k x)
    (hhk : ∀ x, h =ᶠ[𝓝[≠] x] k) : ofMeromorphic hh = ofMeromorphic hk :=
  eq_of_eventually_apply_eq fun x ↦ by
    filter_upwards [eventually_sphereMap_eq (hh x), eventually_sphereMap_eq (hk x), hhk x]
      with y hhy hky hy
    rw [coe_ofMeromorphic, coe_ofMeromorphic, hhy, hky, hy]

/-- A meromorphic function `k` equals `TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic hh`
if and only if it agrees with `h` at the points satisfying a property `p` which holds on a
punctured neighbourhood of every point and at which `h` is continuous. -/
theorem eq_ofMeromorphic_iff {p : X → Prop} (hp : ∀ x, ∀ᶠ y in 𝓝[≠] x, p y)
    (hc : ∀ x, p x → ContinuousAt h x) {k : MeromorphicFunction X} :
    k = ofMeromorphic hh ↔ ∀ x, p x → k x = h x := by
  refine ⟨?_, fun hk ↦ eq_of_forall_apply_eq hp fun y hy ↦ ?_⟩
  · rintro rfl x hx
    exact ofMeromorphic_apply_of_continuousAt hh (hc x hx)
  · exact (hk y hy).trans (ofMeromorphic_apply_of_continuousAt hh (hc y hy)).symm

/-- On a connected Riemann surface, a meromorphic function is the one defined by its finite
part. -/
@[simp]
theorem ofMeromorphic_finitePart [PreconnectedSpace X] (f : MeromorphicFunction X) :
    ofMeromorphic f.meromorphicAt_finitePart = f :=
  DFunLike.coe_injective (sphereMap_finitePart f)

end OfMeromorphic

/-! ### The field operations -/

variable [ConnectedSpace X]

instance : Zero (MeromorphicFunction X) :=
  ⟨ofMeromorphic fun _ ↦ meromorphicAt_const (0 : ℂ) _⟩

instance : One (MeromorphicFunction X) :=
  ⟨ofMeromorphic fun _ ↦ meromorphicAt_const (1 : ℂ) _⟩

instance : Add (MeromorphicFunction X) :=
  ⟨fun f g ↦ ofMeromorphic fun x ↦
    (f.meromorphicAt_finitePart x).add (g.meromorphicAt_finitePart x)⟩

instance : Mul (MeromorphicFunction X) :=
  ⟨fun f g ↦ ofMeromorphic fun x ↦
    (f.meromorphicAt_finitePart x).mul (g.meromorphicAt_finitePart x)⟩

instance : Neg (MeromorphicFunction X) :=
  ⟨fun f ↦ ofMeromorphic fun x ↦ (f.meromorphicAt_finitePart x).neg⟩

instance : Sub (MeromorphicFunction X) :=
  ⟨fun f g ↦ ofMeromorphic fun x ↦
    (f.meromorphicAt_finitePart x).sub (g.meromorphicAt_finitePart x)⟩

instance : Inv (MeromorphicFunction X) :=
  ⟨fun f ↦ ofMeromorphic fun x ↦ (f.meromorphicAt_finitePart x).inv⟩

instance : SMul ℕ (MeromorphicFunction X) :=
  ⟨fun n f ↦ ofMeromorphic fun x ↦ (f.meromorphicAt_finitePart x).const_smul (n : ℂ)⟩

instance : SMul ℤ (MeromorphicFunction X) :=
  ⟨fun n f ↦ ofMeromorphic fun x ↦ (f.meromorphicAt_finitePart x).const_smul (n : ℂ)⟩

instance : Pow (MeromorphicFunction X) ℕ :=
  ⟨fun f n ↦ ofMeromorphic fun x ↦ (f.meromorphicAt_finitePart x).pow n⟩

instance : NatCast (MeromorphicFunction X) :=
  ⟨fun n ↦ ofMeromorphic fun _ ↦ meromorphicAt_const (n : ℂ) _⟩

instance : IntCast (MeromorphicFunction X) :=
  ⟨fun n ↦ ofMeromorphic fun _ ↦ meromorphicAt_const (n : ℂ) _⟩

@[simp]
theorem coe_zero : ⇑(0 : MeromorphicFunction X) = fun _ ↦ ((0 : ℂ) : OnePoint ℂ) :=
  sphereMap_const 0

@[simp]
theorem coe_one : ⇑(1 : MeromorphicFunction X) = fun _ ↦ ((1 : ℂ) : OnePoint ℂ) :=
  sphereMap_const 1

@[simp]
theorem finitePart_zero : (0 : MeromorphicFunction X).finitePart = 0 :=
  funext fun _ ↦ finitePart_of_eq_coe (congrFun coe_zero _)

@[simp]
theorem finitePart_one : (1 : MeromorphicFunction X).finitePart = 1 :=
  funext fun _ ↦ finitePart_of_eq_coe (congrFun coe_one _)

/-- The finite part of `f + g` agrees with the sum of the finite parts of `f` and `g` on a
punctured neighbourhood of every point. -/
theorem finitePart_add_eventuallyEq (f g : MeromorphicFunction X) (x : X) :
    (f + g).finitePart =ᶠ[𝓝[≠] x] f.finitePart + g.finitePart :=
  finitePart_ofMeromorphic_eventuallyEq _ x

/-- The finite part of `f * g` agrees with the product of the finite parts of `f` and `g` on a
punctured neighbourhood of every point. -/
theorem finitePart_mul_eventuallyEq (f g : MeromorphicFunction X) (x : X) :
    (f * g).finitePart =ᶠ[𝓝[≠] x] f.finitePart * g.finitePart :=
  finitePart_ofMeromorphic_eventuallyEq _ x

/-- The finite part of `-f` agrees with the negative of the finite part of `f` on a punctured
neighbourhood of every point. -/
theorem finitePart_neg_eventuallyEq (f : MeromorphicFunction X) (x : X) :
    (-f).finitePart =ᶠ[𝓝[≠] x] -f.finitePart :=
  finitePart_ofMeromorphic_eventuallyEq _ x

/-- The finite part of `f⁻¹` agrees with the inverse of the finite part of `f` on a punctured
neighbourhood of every point. -/
theorem finitePart_inv_eventuallyEq (f : MeromorphicFunction X) (x : X) :
    f⁻¹.finitePart =ᶠ[𝓝[≠] x] f.finitePart⁻¹ :=
  finitePart_ofMeromorphic_eventuallyEq _ x

/-! ### The commutative ring structure -/

/-- The meromorphic functions on a connected Riemann surface form a commutative ring. -/
instance instCommRing : CommRing (MeromorphicFunction X) :=
  -- The ring axioms are transferred along the injective map sending `f` to the germs of its finite
  -- part on the punctured neighbourhoods of the points, which is compatible with the operations.
  have hinj : Injective fun (f : MeromorphicFunction X) (x : X) ↦
      (f.finitePart : Germ (𝓝[≠] x) ℂ) := fun _ _ h ↦
    eq_of_eventuallyEq_finitePart fun x ↦ Germ.coe_eq.1 (congrFun h x)
  have hof {h : X → ℂ} (hh : ∀ x, MeromorphicAt h x) :
      (fun x ↦ ((ofMeromorphic hh).finitePart : Germ (𝓝[≠] x) ℂ)) =
        fun x ↦ (h : Germ (𝓝[≠] x) ℂ) :=
    funext fun x ↦ Germ.coe_eq.2 (finitePart_ofMeromorphic_eventuallyEq hh x)
  hinj.commRing _ (hof _) (hof _) (fun _ _ ↦ hof _) (fun _ _ ↦ hof _) (fun _ ↦ hof _)
    (fun _ _ ↦ hof _)
    (fun n _ ↦ (hof _).trans (funext fun _ ↦ by
      rw [Nat.cast_smul_eq_nsmul, Germ.coe_smul, Pi.smul_apply]))
    (fun n _ ↦ (hof _).trans (funext fun _ ↦ by
      rw [Int.cast_smul_eq_zsmul, Germ.coe_smul, Pi.smul_apply]))
    (fun _ _ ↦ hof _) (fun _ ↦ hof _) (fun _ ↦ hof _)

/-! ### The field structure -/

/-- The zeros of a nonzero meromorphic function on a connected Riemann surface are isolated, as
are its poles, so its finite part vanishes at no point of a punctured neighbourhood of any
point. -/
theorem eventually_finitePart_ne_zero (hf : f ≠ 0) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, f.finitePart y ≠ 0 := by
  have h0 : ⇑f ≠ fun _ ↦ ((0 : ℂ) : OnePoint ℂ) := by
    rw [← coe_zero]
    exact fun h ↦ hf (DFunLike.coe_injective h)
  filter_upwards [f.eventually_ne_infty x, eventually_apply_ne_of_ne_const f.mdifferentiable h0 x]
    with y hy hy0 hfy
  exact hy0 (by rw [← coe_finitePart hy, hfy])

/-- The meromorphic functions on a connected Riemann surface form a field. -/
instance instField : Field (MeromorphicFunction X) where
  __ := instCommRing
  exists_pair_ne := ⟨0, 1, fun h ↦ by
    simpa using congrFun (congrArg DFunLike.coe h) (Classical.arbitrary X)⟩
  mul_inv_cancel f hf := by
    refine eq_of_eventuallyEq_finitePart fun x ↦ ?_
    filter_upwards [finitePart_mul_eventuallyEq f f⁻¹ x, finitePart_inv_eventuallyEq f x,
      eventually_finitePart_ne_zero hf x] with y hmul hinv hy
    simp [hmul, hinv, hy]
  inv_zero := by
    refine eq_of_eventuallyEq_finitePart fun x ↦ ?_
    filter_upwards [finitePart_inv_eventuallyEq (0 : MeromorphicFunction X) x] with y hy
    simp [hy]
  nnqsmul := _
  nnqsmul_def _ _ := rfl
  qsmul := _
  qsmul_def _ _ := rfl

/-! ### The defining properties of the operations -/

/-- **The defining property of addition.** On a connected Riemann surface, `f + g` is the unique
meromorphic function whose value at every point where `f` and `g` are both finite is the sum of
their values. -/
theorem eq_add_iff {k : MeromorphicFunction X} :
    k = f + g ↔ ∀ x, f x ≠ ∞ → g x ≠ ∞ → k x = ↑(f.finitePart x + g.finitePart x) :=
  (eq_ofMeromorphic_iff _ (fun x ↦ (f.eventually_ne_infty x).and (g.eventually_ne_infty x))
    fun _ hy ↦ (continuousAt_finitePart hy.1).add (continuousAt_finitePart hy.2)).trans
    (forall_congr' fun _ ↦ and_imp)

/-- **The defining property of multiplication.** On a connected Riemann surface, `f * g` is the
unique meromorphic function whose value at every point where `f` and `g` are both finite is the
product of their values. -/
theorem eq_mul_iff {k : MeromorphicFunction X} :
    k = f * g ↔ ∀ x, f x ≠ ∞ → g x ≠ ∞ → k x = ↑(f.finitePart x * g.finitePart x) :=
  (eq_ofMeromorphic_iff _ (fun x ↦ (f.eventually_ne_infty x).and (g.eventually_ne_infty x))
    fun _ hy ↦ (continuousAt_finitePart hy.1).mul (continuousAt_finitePart hy.2)).trans
    (forall_congr' fun _ ↦ and_imp)

/-- **The defining property of negation.** On a connected Riemann surface, `-f` is the unique
meromorphic function whose value at every point where `f` is finite is the negative of the value of
`f`. -/
theorem eq_neg_iff {k : MeromorphicFunction X} :
    k = -f ↔ ∀ x, f x ≠ ∞ → k x = ↑(-f.finitePart x) :=
  eq_ofMeromorphic_iff _ f.eventually_ne_infty fun _ hy ↦ (continuousAt_finitePart hy).neg

/-- **The defining property of the inverse.** On a connected Riemann surface, the inverse of a
nonzero meromorphic function `f` is the unique meromorphic function whose value at every point
where `f` is finite and nonzero is the inverse of the value of `f`. -/
theorem eq_inv_iff (hf : f ≠ 0) {k : MeromorphicFunction X} :
    k = f⁻¹ ↔ ∀ x, f x ≠ ∞ → f x ≠ ((0 : ℂ) : OnePoint ℂ) → k x = ↑(f.finitePart x)⁻¹ := by
  refine (eq_ofMeromorphic_iff _ (p := fun y ↦ f y ≠ ∞ ∧ f y ≠ ((0 : ℂ) : OnePoint ℂ))
    (fun x ↦ ?_) fun y hy ↦ ?_).trans (forall_congr' fun _ ↦ and_imp)
  · filter_upwards [f.eventually_ne_infty x, eventually_finitePart_ne_zero hf x] with y hy hy0
    exact ⟨hy, fun h ↦ hy0 (finitePart_of_eq_coe h)⟩
  · exact (continuousAt_finitePart hy.1).inv₀ fun h ↦ hy.2 (by rw [← coe_finitePart hy.1, h])

/-! ### The `ℂ`-algebra structure -/

/-- The meromorphic functions on a connected Riemann surface form a `ℂ`-algebra, `ℂ` acting
through the constant functions. -/
instance instAlgebra : Algebra ℂ (MeromorphicFunction X) :=
  RingHom.toAlgebra
    { toFun c := ofMeromorphic fun _ ↦ meromorphicAt_const c _
      map_one' := rfl
      map_zero' := rfl
      map_add' a b := eq_of_eventuallyEq_finitePart fun x ↦ by
        filter_upwards [finitePart_add_eventuallyEq (ofMeromorphic fun _ ↦ meromorphicAt_const a _)
          (ofMeromorphic fun _ ↦ meromorphicAt_const b _) x] with y hy
        simp [hy, finitePart_of_eq_coe]
      map_mul' a b := eq_of_eventuallyEq_finitePart fun x ↦ by
        filter_upwards [finitePart_mul_eventuallyEq (ofMeromorphic fun _ ↦ meromorphicAt_const a _)
          (ofMeromorphic fun _ ↦ meromorphicAt_const b _) x] with y hy
        simp [hy, finitePart_of_eq_coe] }

@[simp]
theorem coe_algebraMap (c : ℂ) :
    ⇑(algebraMap ℂ (MeromorphicFunction X) c) = fun _ ↦ (c : OnePoint ℂ) :=
  sphereMap_const c

@[simp]
theorem finitePart_algebraMap (c : ℂ) :
    (algebraMap ℂ (MeromorphicFunction X) c).finitePart = fun _ ↦ c :=
  funext fun _ ↦ finitePart_of_eq_coe (congrFun (coe_algebraMap c) _)

/-! ### `ofMeromorphic` and the operations

On a connected Riemann surface, `TauCeti.RiemannSurface.MeromorphicFunction.ofMeromorphic` sends
constants, sums, products, negatives, differences, inverses and powers of functions `X → ℂ` to the
corresponding operations on meromorphic functions. Apart from the constants, these lemmas are not
simp lemmas: their left-hand sides do not determine the meromorphy proofs of the operands, so `simp`
could not discharge them. Instantiate them instead, as in `simp [ofMeromorphic_add hh hk]`. -/

section OfMeromorphicOperations

variable {h k : X → ℂ} (hh : ∀ x, MeromorphicAt h x) (hk : ∀ x, MeromorphicAt k x)

@[simp]
theorem ofMeromorphic_const (c : ℂ) :
    ofMeromorphic (fun _ ↦ meromorphicAt_const c _) = algebraMap ℂ (MeromorphicFunction X) c :=
  rfl

theorem ofMeromorphic_add :
    ofMeromorphic (fun x ↦ (hh x).add (hk x)) = ofMeromorphic hh + ofMeromorphic hk :=
  ofMeromorphic_congr _ _ fun x ↦ ((finitePart_ofMeromorphic_eventuallyEq hh x).add
    (finitePart_ofMeromorphic_eventuallyEq hk x)).symm

theorem ofMeromorphic_mul :
    ofMeromorphic (fun x ↦ (hh x).mul (hk x)) = ofMeromorphic hh * ofMeromorphic hk :=
  ofMeromorphic_congr _ _ fun x ↦ ((finitePart_ofMeromorphic_eventuallyEq hh x).mul
    (finitePart_ofMeromorphic_eventuallyEq hk x)).symm

theorem ofMeromorphic_neg : ofMeromorphic (fun x ↦ (hh x).neg) = -ofMeromorphic hh :=
  ofMeromorphic_congr _ _ fun x ↦ (finitePart_ofMeromorphic_eventuallyEq hh x).neg.symm

theorem ofMeromorphic_sub :
    ofMeromorphic (fun x ↦ (hh x).sub (hk x)) = ofMeromorphic hh - ofMeromorphic hk :=
  ofMeromorphic_congr _ _ fun x ↦ ((finitePart_ofMeromorphic_eventuallyEq hh x).sub
    (finitePart_ofMeromorphic_eventuallyEq hk x)).symm

theorem ofMeromorphic_inv : ofMeromorphic (fun x ↦ (hh x).inv) = (ofMeromorphic hh)⁻¹ :=
  ofMeromorphic_congr _ _ fun x ↦ (finitePart_ofMeromorphic_eventuallyEq hh x).inv.symm

theorem ofMeromorphic_pow (n : ℕ) :
    ofMeromorphic (fun x ↦ (hh x).pow n) = ofMeromorphic hh ^ n :=
  ofMeromorphic_congr _ _ fun x ↦ ((finitePart_ofMeromorphic_eventuallyEq hh x).pow_const n).symm

end OfMeromorphicOperations

/-! ### Values of the operations

At a point where the operands are finite, the operations on meromorphic functions are computed
pointwise. Each operation has two forms: one for operands known to be finite, in terms of their
finite parts, and one (`_of_eq_coe`) for operands with known finite values. At a pole of `f`, its
inverse vanishes. -/

/-- At a point where `f` and `g` are finite, `f + g` takes the sum of their values. -/
theorem add_apply (hf : f x ≠ ∞) (hg : g x ≠ ∞) :
    (f + g) x = ↑(f.finitePart x + g.finitePart x) :=
  eq_add_iff.1 rfl x hf hg

/-- If `f` and `g` take the values `a` and `b` at `x`, then `f + g` takes the value `a + b`. -/
theorem add_apply_of_eq_coe {a b : ℂ} (hf : f x = a) (hg : g x = b) : (f + g) x = ↑(a + b) := by
  rw [add_apply (by simp [hf]) (by simp [hg]), finitePart_of_eq_coe hf, finitePart_of_eq_coe hg]

/-- At a point where `f` and `g` are finite, `f * g` takes the product of their values. -/
theorem mul_apply (hf : f x ≠ ∞) (hg : g x ≠ ∞) :
    (f * g) x = ↑(f.finitePart x * g.finitePart x) :=
  eq_mul_iff.1 rfl x hf hg

/-- If `f` and `g` take the values `a` and `b` at `x`, then `f * g` takes the value `a * b`. -/
theorem mul_apply_of_eq_coe {a b : ℂ} (hf : f x = a) (hg : g x = b) : (f * g) x = ↑(a * b) := by
  rw [mul_apply (by simp [hf]) (by simp [hg]), finitePart_of_eq_coe hf, finitePart_of_eq_coe hg]

/-- At a point where `f` is finite, `-f` takes the negative of its value. -/
theorem neg_apply (hf : f x ≠ ∞) : (-f) x = ↑(-f.finitePart x) :=
  eq_neg_iff.1 rfl x hf

/-- If `f` takes the value `a` at `x`, then `-f` takes the value `-a`. -/
theorem neg_apply_of_eq_coe {a : ℂ} (hf : f x = a) : (-f) x = ↑(-a) := by
  rw [neg_apply (by simp [hf]), finitePart_of_eq_coe hf]

/-- If `f` and `g` take the values `a` and `b` at `x`, then `f - g` takes the value `a - b`. -/
theorem sub_apply_of_eq_coe {a b : ℂ} (hf : f x = a) (hg : g x = b) : (f - g) x = ↑(a - b) := by
  rw [sub_eq_add_neg, add_apply_of_eq_coe hf (neg_apply_of_eq_coe hg), sub_eq_add_neg]

/-- At a point where `f` and `g` are finite, `f - g` takes the difference of their values. -/
theorem sub_apply (hf : f x ≠ ∞) (hg : g x ≠ ∞) :
    (f - g) x = ↑(f.finitePart x - g.finitePart x) :=
  sub_apply_of_eq_coe (coe_finitePart hf).symm (coe_finitePart hg).symm

/-- At a point where `f` is finite and nonzero, `f⁻¹` takes the inverse of its value. -/
theorem inv_apply (hf : f x ≠ ∞) (hf0 : f x ≠ ((0 : ℂ) : OnePoint ℂ)) :
    f⁻¹ x = ↑(f.finitePart x)⁻¹ := by
  refine (eq_inv_iff (fun h ↦ hf0 ?_)).1 rfl x hf hf0
  rw [h, coe_zero]

/-- If `f` takes a nonzero value `a` at `x`, then `f⁻¹` takes the value `a⁻¹`. -/
theorem inv_apply_of_eq_coe {a : ℂ} (hf : f x = a) (ha : a ≠ 0) : f⁻¹ x = ↑a⁻¹ := by
  rw [inv_apply (by simp [hf]) (by simpa [hf] using ha), finitePart_of_eq_coe hf]

/-- If `f` takes the value `a` at `x`, then `f ^ n` takes the value `a ^ n`. -/
theorem pow_apply_of_eq_coe {a : ℂ} (hf : f x = a) (n : ℕ) : (f ^ n) x = ↑(a ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_apply_of_eq_coe ih hf, pow_succ]

/-- At a point where `f` is finite, `f ^ n` takes the `n`-th power of its value. -/
theorem pow_apply (hf : f x ≠ ∞) (n : ℕ) : (f ^ n) x = ↑(f.finitePart x ^ n) :=
  pow_apply_of_eq_coe (coe_finitePart hf).symm n

/-- If `f` takes a nonzero value `a` at `x`, then `f ^ n` takes the value `a ^ n`, for every
integer `n`. -/
theorem zpow_apply_of_eq_coe {a : ℂ} (hf : f x = a) (ha : a ≠ 0) (n : ℤ) :
    (f ^ n) x = ↑(a ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using pow_apply_of_eq_coe hf m
  · rw [zpow_neg, zpow_natCast, inv_apply_of_eq_coe (pow_apply_of_eq_coe hf m) (pow_ne_zero _ ha),
      zpow_neg, zpow_natCast]

/-- At a point where `f` is finite and nonzero, `f ^ n` takes the `n`-th power of its value, for
every integer `n`. -/
theorem zpow_apply (hf : f x ≠ ∞) (hf0 : f x ≠ ((0 : ℂ) : OnePoint ℂ)) (n : ℤ) :
    (f ^ n) x = ↑(f.finitePart x ^ n) :=
  zpow_apply_of_eq_coe (coe_finitePart hf).symm
    (fun h0 ↦ hf0 (by rw [← coe_finitePart hf, h0])) n

/-- If each `f i` takes the value `a i` at `x`, then the product of the `f i` takes the product of
the `a i`. -/
theorem prod_apply_of_eq_coe {ι : Type*} {s : Finset ι} {f : ι → MeromorphicFunction X}
    {a : ι → ℂ} (hf : ∀ i ∈ s, f i x = a i) : (∏ i ∈ s, f i) x = ↑(∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      mul_apply_of_eq_coe (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))]

/-- At a point where each `f i` is finite, the product of the `f i` takes the product of their
values. -/
theorem prod_apply {ι : Type*} {s : Finset ι} {f : ι → MeromorphicFunction X}
    (hf : ∀ i ∈ s, f i x ≠ ∞) : (∏ i ∈ s, f i) x = ↑(∏ i ∈ s, (f i).finitePart x) :=
  prod_apply_of_eq_coe fun i hi ↦ (coe_finitePart (hf i hi)).symm

/-- **The inverse vanishes at the poles.** At a pole of `f`, the meromorphic function `f⁻¹`
takes the value `0`. -/
theorem inv_apply_of_eq_infty (hf : f x = ∞) : f⁻¹ x = ((0 : ℂ) : OnePoint ℂ) := by
  -- Near the pole, `f⁻¹` is `f` read in the inverted chart of the sphere, which is continuous
  -- at `∞` with value `0`.
  have hinv : ContinuousAt (fun y ↦ invChart (f y)) x := by
    refine ContinuousAt.comp (g := invChart) ?_ f.continuous.continuousAt
    rw [hf]
    exact invChart.continuousAt (by simp)
  have hcont : Tendsto (fun y ↦ ((invChart (f y) : ℂ) : OnePoint ℂ)) (𝓝 x)
      (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
    have h := (OnePoint.continuous_coe.continuousAt.comp hinv).tendsto
    rwa [comp_apply, hf, invChart_infty] at h
  have hne0 : ∀ᶠ y in 𝓝 x, f y ≠ ((0 : ℂ) : OnePoint ℂ) :=
    f.continuous.continuousAt.eventually_ne (by simp [hf])
  refine apply_eq_of_tendsto (hcont.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [f.eventually_ne_infty x, nhdsWithin_le_nhds hne0] with y hy hy0
  rw [inv_apply hy hy0, finitePart_def, ← inv_invChart, inv_inv]

/-! ### Finiteness of zeros and poles, and the maximum principle -/

section Compact

variable [CompactSpace X]

/-- **A meromorphic function on a compact connected Riemann surface has finitely many poles.** -/
theorem finite_setOf_eq_infty (f : MeromorphicFunction X) : {x | f x = ∞}.Finite := by
  have h : {x | f x ≠ ∞} ∈ Filter.codiscrete X :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.2 f.eventually_ne_infty
  exact (isCompact_univ.finite_sdiff_of_mem_codiscreteWithin h).subset fun y hy ↦
    ⟨mem_univ y, (· hy)⟩

/-- **A nonzero meromorphic function on a compact connected Riemann surface has finitely many
zeros.** -/
theorem finite_setOf_eq_zero (hf : f ≠ 0) : {x | f x = ((0 : ℂ) : OnePoint ℂ)}.Finite := by
  have h : {x | f x ≠ ((0 : ℂ) : OnePoint ℂ)} ∈ Filter.codiscrete X := by
    refine eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x ↦ ?_
    filter_upwards [f.eventually_ne_infty x, eventually_finitePart_ne_zero hf x] with y hy hy0
    exact fun h ↦ hy0 (finitePart_of_eq_coe h)
  exact (isCompact_univ.finite_sdiff_of_mem_codiscreteWithin h).subset fun y hy ↦
    ⟨mem_univ y, (· hy)⟩

/-- **The maximum principle.** A meromorphic function without poles on a compact connected
Riemann surface is constant. -/
theorem exists_algebraMap_eq_of_forall_ne_infty (h : ∀ x, f x ≠ ∞) :
    ∃ c : ℂ, algebraMap ℂ (MeromorphicFunction X) c = f := by
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.finitePart := fun x ↦
    (mdifferentiableAt_atlas (Or.inl rfl) (by simpa using h x)).comp x (f.mdifferentiable x)
  obtain ⟨c, hc⟩ := MDifferentiable.exists_eq_const_of_compactSpace hmd
  refine ⟨c, ext fun x ↦ ?_⟩
  rw [coe_algebraMap, ← coe_finitePart (h x), hc, Function.const_apply]

end Compact

end MeromorphicFunction

end TauCeti.RiemannSurface
