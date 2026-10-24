/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField
import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import TauCeti.Analysis.Complex.RiemannSurface.OpenMapping
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Pulling meromorphic functions back along nonconstant holomorphic maps

Let `φ : X → Y` be a nonconstant holomorphic map between connected Riemann surfaces. Composing a
meromorphic function `f : Y → OnePoint ℂ` with `φ` gives a holomorphic map `f ∘ φ : X → OnePoint ℂ`,
and this is again a meromorphic function on `X`: it is not the constant map `∞`, because by the open
mapping theorem the image of `φ` contains a neighbourhood of each of its points, while the poles of
`f` are isolated (`TauCeti.RiemannSurface.MeromorphicFunction.comap`). The pullback `f ↦ f ∘ φ`
respects the field operations, since these are characterized by their values away from the poles,
and so it is a homomorphism of `ℂ`-algebras
`TauCeti.RiemannSurface.MeromorphicFunction.comapₐ φ : M(Y) →ₐ[ℂ] M(X)`, injective because `M(Y)`
is a field. Pullback is functorial: it sends the identity to the identity and a composite to the
composite in the opposite order.

For a nonconstant holomorphic `β : X → OnePoint ℂ` on a connected Riemann surface `X`, this is the
embedding `M(OnePoint ℂ) ↪ M(X)` of the function field of the Riemann sphere into that of `X`.
Composed with the classical identification of `M(OnePoint ℂ)` with the rational function field
`ℂ(t)`, it is the embedding `ℂ(t) ↪ M(X)` induced by `β`.

Orders of vanishing pull back with the local multiplicity of `φ` as a factor: the order of
`f ∘ φ` at `x` is the order of `f` at `φ x` times the local multiplicity of `φ` at `x`
(`TauCeti.RiemannSurface.MeromorphicFunction.meromorphicOrderAt_finitePart_comap`). This is the
relation between the valuations of `M(X)` and of `M(Y)` at points lying over one another.

## Main definitions

* `TauCeti.RiemannSurface.MeromorphicFunction.comap`: the pullback `f ∘ φ` of a meromorphic
  function along a nonconstant holomorphic map of connected Riemann surfaces.
* `TauCeti.RiemannSurface.MeromorphicFunction.comapₐ`: the pullback as a homomorphism of
  `ℂ`-algebras.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.comapₐ_injective`: the pullback is injective.
* `TauCeti.RiemannSurface.MeromorphicFunction.comapₐ_id` and
  `TauCeti.RiemannSurface.MeromorphicFunction.comapₐ_comp`: functoriality.
* `TauCeti.RiemannSurface.MeromorphicFunction.meromorphicOrderAt_finitePart_comap`: the order of a
  pullback.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §8 (the pullback of meromorphic functions along a nonconstant holomorphic map, a monomorphism of
  fields).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (pullbacks of meromorphic functions and the
  order of a pullback).
-/

public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) 1 Z]

/-! ### The pullback of a meromorphic function -/

section Comap

variable [PreconnectedSpace X] [PreconnectedSpace Y] (φ : X → Y)
  (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hne : ∃ x₁ x₂, φ x₁ ≠ φ x₂)

include hφ hne in
/-- A meromorphic function on a connected Riemann surface, composed with a nonconstant holomorphic
map from a connected Riemann surface, is not the constant map `∞`: by the open mapping theorem
the image of the map is a neighbourhood of each of its points, and these punctured neighbourhoods
contain points which are not poles. -/
private theorem comp_ne_infty (f : MeromorphicFunction Y) : ⇑f ∘ φ ≠ fun _ ↦ ∞ := by
  obtain ⟨x₁, x₂, h⟩ := hne
  have hrange : range φ ∈ 𝓝 (φ x₁) :=
    nhds_le_map_nhds_of_not_eventuallyConst (.of_forall fun y ↦ hφ y)
      (not_eventuallyConst_of_ne hφ h x₁) range_mem_map
  have := (chartAt ℂ (φ x₁)).nhdsNE_neBot (mem_chart_source ℂ (φ x₁))
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ :=
    Filter.nonempty_of_mem (inter_mem (nhdsWithin_le_nhds hrange) (f.eventually_ne_infty (φ x₁)))
  exact fun hinf ↦ hx (congrFun hinf x)

include hφ hne in
/-- The **pullback** `f ∘ φ` of a meromorphic function `f` on `Y` along a nonconstant holomorphic
map `φ : X → Y` of connected Riemann surfaces. It is a homomorphism of `ℂ`-algebras,
`TauCeti.RiemannSurface.MeromorphicFunction.comapₐ`. -/
def comap (f : MeromorphicFunction Y) : MeromorphicFunction X where
  toFun := f ∘ φ
  mdifferentiable' := f.mdifferentiable.comp hφ
  ne_infty' := comp_ne_infty φ hφ hne f

@[simp]
theorem coe_comap (f : MeromorphicFunction Y) : ⇑(comap φ hφ hne f) = f ∘ φ :=
  (rfl)

@[simp]
theorem comap_apply (f : MeromorphicFunction Y) (x : X) : comap φ hφ hne f x = f (φ x) :=
  (rfl)

@[simp]
theorem finitePart_comap (f : MeromorphicFunction Y) :
    (comap φ hφ hne f).finitePart = f.finitePart ∘ φ :=
  funext fun _ ↦ by simp only [finitePart_def, comap_apply, comp_apply]

/-- **The order of a pullback.** The order of `f ∘ φ` at `x` is the order of `f` at `φ x` times
the local multiplicity of `φ` at `x`. -/
theorem meromorphicOrderAt_finitePart_comap (f : MeromorphicFunction Y) (x : X) :
    meromorphicOrderAt (comap φ hφ hne f).finitePart x =
      meromorphicOrderAt f.finitePart (φ x) * localMultiplicity φ x := by
  obtain ⟨_, _, h⟩ := hne
  rw [finitePart_comap]
  exact meromorphicOrderAt_comp (f.meromorphicAt_finitePart (φ x)) (.of_forall fun y ↦ hφ y)
    (not_eventuallyConst_of_ne hφ h x)

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem comap_id (hne : ∃ x₁ x₂ : Y, x₁ ≠ x₂) (f : MeromorphicFunction Y) :
    comap id mdifferentiable_id hne f = f :=
  (rfl)

/-- Pulling back along `ψ` and then along `φ` is pulling back along `ψ ∘ φ`. -/
theorem comap_comap [PreconnectedSpace Z] {ψ : Y → Z} (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    (hψne : ∃ y₁ y₂, ψ y₁ ≠ ψ y₂) (hψφne : ∃ x₁ x₂, ψ (φ x₁) ≠ ψ (φ x₂))
    (f : MeromorphicFunction Z) :
    comap φ hφ hne (comap ψ hψ hψne f) = comap (ψ ∘ φ) (hψ.comp hφ) hψφne f :=
  (rfl)

end Comap

/-! ### The pullback as a homomorphism of `ℂ`-algebras -/

section ComapAlgHom

variable [ConnectedSpace X] [ConnectedSpace Y] (φ : X → Y)
  (hφ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ) (hne : ∃ x₁ x₂, φ x₁ ≠ φ x₂)

include hφ hne in
/-- The pullback of meromorphic functions along a nonconstant holomorphic map `φ : X → Y` of
connected Riemann surfaces, as a homomorphism of `ℂ`-algebras `M(Y) →ₐ[ℂ] M(X)`, `f ↦ f ∘ φ`. -/
def comapₐ : MeromorphicFunction Y →ₐ[ℂ] MeromorphicFunction X where
  toFun := comap φ hφ hne
  map_one' := ext fun _ ↦ by simp
  map_mul' f g := eq_mul_iff.2 fun x hf hg ↦ by
    simpa only [comap_apply, finitePart_comap, comp_apply] using eq_mul_iff.1 rfl (φ x) hf hg
  map_zero' := ext fun _ ↦ by simp
  map_add' f g := eq_add_iff.2 fun x hf hg ↦ by
    simpa only [comap_apply, finitePart_comap, comp_apply] using eq_add_iff.1 rfl (φ x) hf hg
  commutes' c := ext fun _ ↦ by simp

@[simp]
theorem comapₐ_apply (f : MeromorphicFunction Y) : comapₐ φ hφ hne f = comap φ hφ hne f :=
  (rfl)

@[simp]
theorem comap_zero : comap φ hφ hne 0 = 0 :=
  map_zero (comapₐ φ hφ hne)

@[simp]
theorem comap_one : comap φ hφ hne 1 = 1 :=
  map_one (comapₐ φ hφ hne)

@[simp]
theorem comap_add (f g : MeromorphicFunction Y) :
    comap φ hφ hne (f + g) = comap φ hφ hne f + comap φ hφ hne g :=
  map_add (comapₐ φ hφ hne) f g

@[simp]
theorem comap_mul (f g : MeromorphicFunction Y) :
    comap φ hφ hne (f * g) = comap φ hφ hne f * comap φ hφ hne g :=
  map_mul (comapₐ φ hφ hne) f g

@[simp]
theorem comap_neg (f : MeromorphicFunction Y) : comap φ hφ hne (-f) = -comap φ hφ hne f :=
  map_neg (comapₐ φ hφ hne) f

@[simp]
theorem comap_sub (f g : MeromorphicFunction Y) :
    comap φ hφ hne (f - g) = comap φ hφ hne f - comap φ hφ hne g :=
  map_sub (comapₐ φ hφ hne) f g

@[simp]
theorem comap_inv (f : MeromorphicFunction Y) : comap φ hφ hne f⁻¹ = (comap φ hφ hne f)⁻¹ :=
  map_inv₀ (comapₐ φ hφ hne) f

@[simp]
theorem comap_div (f g : MeromorphicFunction Y) :
    comap φ hφ hne (f / g) = comap φ hφ hne f / comap φ hφ hne g :=
  map_div₀ (comapₐ φ hφ hne) f g

@[simp]
theorem comap_pow (f : MeromorphicFunction Y) (n : ℕ) :
    comap φ hφ hne (f ^ n) = comap φ hφ hne f ^ n :=
  map_pow (comapₐ φ hφ hne) f n

@[simp]
theorem comap_algebraMap (c : ℂ) :
    comap φ hφ hne (algebraMap ℂ (MeromorphicFunction Y) c) =
      algebraMap ℂ (MeromorphicFunction X) c :=
  (comapₐ φ hφ hne).commutes c

/-- **The pullback is a field embedding.** Pulling meromorphic functions back along a
nonconstant holomorphic map of connected Riemann surfaces is injective. -/
theorem comapₐ_injective : Injective (comapₐ φ hφ hne) :=
  (comapₐ φ hφ hne).toRingHom.injective

@[simp]
theorem comapₐ_id (hne : ∃ x₁ x₂ : Y, x₁ ≠ x₂) :
    comapₐ id mdifferentiable_id hne = AlgHom.id ℂ (MeromorphicFunction Y) :=
  AlgHom.ext fun _ ↦ comap_id hne _

/-- **Functoriality of the pullback.** Pulling back along `ψ ∘ φ` is pulling back along `ψ` and
then along `φ`. -/
theorem comapₐ_comp [ConnectedSpace Z] {ψ : Y → Z} (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ)
    (hψne : ∃ y₁ y₂, ψ y₁ ≠ ψ y₂) (hψφne : ∃ x₁ x₂, ψ (φ x₁) ≠ ψ (φ x₂)) :
    comapₐ (ψ ∘ φ) (hψ.comp hφ) hψφne = (comapₐ φ hφ hne).comp (comapₐ ψ hψ hψne) :=
  AlgHom.ext fun f ↦ (comap_comap φ hφ hne hψ hψne hψφne f).symm

end ComapAlgHom

end TauCeti.RiemannSurface.MeromorphicFunction
