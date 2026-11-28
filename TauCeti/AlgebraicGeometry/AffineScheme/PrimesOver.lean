/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import Mathlib.RingTheory.Ideal.Over

/-!
# Fibres over a point of an affine open

Let `f : X ⟶ Y` be a morphism of schemes, `V ⊆ Y` an affine open and `U = f⁻¹ V` affine. Through
the ring map `f^* : Γ(Y, V) → Γ(X, U)`, the points of `X` over a point `y ∈ V` are the primes of
`Γ(X, U)` lying over the prime `p_y` of `Γ(Y, V)` corresponding to `y`
(`AlgebraicGeometry.IsAffineOpen.preimageSingletonEquivPrimesOver`). This is how the fibre of a
finite (hence affine) morphism over a point is read off from the rings of an affine
neighbourhood, and it rests on Mathlib's `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`.

Adapted from the [lookahead formalization](https://github.com/roed-math/TauCeti-w2-fresh/tree/678c1bad7a8c53d6cffb49946b9fefc73d4c0435).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

variable {V : Y.Opens} (hV : IsAffineOpen V) (f : X ⟶ Y) {U : X.Opens} (hU : IsAffineOpen U)
  (hUV : f ⁻¹ᵁ V = U) {y : Y} (hy : y ∈ V)

/-- The points of `X` over `y ∈ V`, for affine opens `V ⊆ Y` and `U = f⁻¹ V ⊆ X`, are the primes of
`Γ(X, U)` over the prime of `y` in `Γ(Y, V)`, through `f^* : Γ(Y, V) → Γ(X, U)`. -/
noncomputable def IsAffineOpen.preimageSingletonEquivPrimesOver :
    letI := (f.appLE V U hUV.ge).hom.toAlgebra
    (f ⁻¹' {y} : Set X) ≃ (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U) :=
  letI := (f.appLE V U hUV.ge).hom.toAlgebra
  have hmem (x : X) (hx : f x = y) : x ∈ U := by
    rw [← hUV, Scheme.Hom.mem_preimage, hx]
    exact hy
  -- The prime of `x ∈ U` contracts to the prime of `f x`.
  have hcomap (x : X) (hx : x ∈ U) : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.under Γ(Y, V) =
      (hV.primeIdealOf ⟨f x, hUV.ge hx⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV.ge hx).asIdeal)
  { toFun x :=
      ⟨(hU.primeIdealOf ⟨x, hmem x x.property⟩).asIdeal, inferInstance, ⟨by
        rw [hcomap]
        congr
        exact x.property.symm⟩⟩
    invFun q :=
      ⟨hU.fromSpec ⟨q.val, q.property.1⟩, by
        have h := hcomap (hU.fromSpec ⟨q.val, q.property.1⟩) (hU.fromSpec_mem _)
        rw [hU.primeIdealOf_fromSpec _ (hU.fromSpec_mem _)] at h
        have := q.property.2
        rw [← Ideal.over_def q.val (hV.primeIdealOf ⟨y, hy⟩).asIdeal] at h
        have h' := congr(hV.fromSpec $(PrimeSpectrum.ext h))
        rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h'
        exact h'.symm⟩
    left_inv x := Subtype.ext <| hU.fromSpec_primeIdealOf ⟨x, _⟩
    right_inv q := Subtype.ext <|
      congr($(hU.primeIdealOf_fromSpec ⟨q.val, q.property.1⟩ (hU.fromSpec_mem _)).asIdeal) }

/-- The fibre-to-prime correspondence sends a point to its prime on the source affine open. -/
@[simp]
theorem IsAffineOpen.coe_preimageSingletonEquivPrimesOver_apply (x : (f ⁻¹' {y} : Set X)) :
    (hV.preimageSingletonEquivPrimesOver f hU hUV hy x).val =
      (hU.primeIdealOf ⟨x, by
        rw [← hUV, Scheme.Hom.mem_preimage, x.property]
        exact hy⟩).asIdeal :=
  (rfl)

/-- The inverse correspondence sends a prime to its point on the source affine open. -/
@[simp]
theorem IsAffineOpen.coe_preimageSingletonEquivPrimesOver_symm_apply
    (q : letI := (f.appLE V U hUV.ge).hom.toAlgebra
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primesOver Γ(X, U)) :
    ((hV.preimageSingletonEquivPrimesOver f hU hUV hy).symm q).val =
      hU.fromSpec ⟨q.val, q.property.1⟩ :=
  (rfl)

end AlgebraicGeometry
