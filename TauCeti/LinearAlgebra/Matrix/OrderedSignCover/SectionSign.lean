/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.Reindex
public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Section signs of homomorphisms of ordered sign covers

Let `B : Matrix I I ℤ` and `B' : Matrix J J ℤ` be Gram matrices on linearly ordered finite sets,
with ordered sign covers `Matrix.SignCover B` and `Matrix.SignCover B'`, and let
`g : (I → ℤ) →ₗ[ℤ] (J → ℤ)`. A homomorphism `φ : SignCover B →* SignCover B'` is *compatible*
with `g` when it fixes the kernel `ℤˣ`, `φ (s, 1) = (s, 1)`, and lies over `g`, so that `φ x`
lies over `g` of the lattice vector of `x`. Such a `φ` sends the canonical lift `(1, a)` of a
lattice vector `a` to a lift of `g a`, so

`φ (1, a) = s_φ(a) (1, g a)`

for a unique sign `s_φ(a)`, the section sign `Matrix.SignCover.sectionSign φ a`
(`Matrix.SignCover.apply_canonicalSection`). Multiplicativity of `φ` says exactly that `s_φ`
relates the ordered sign `ε` of `B` to the pullback along `g` of the ordered sign `ε'` of `B'`:

`ε(a, b) s_φ(a + b) = ε'(g a, g b) s_φ(a) s_φ(b)`

(`Matrix.SignCover.negOnePow_orderedSignForm_mul_sectionSign_add`). This is the identity that lets
a compatible lift act on the signed shell Lie algebra, whose root vectors are indexed by the
canonical lifts: see `TauCeti.Algebra.Lie.NormTwoShell.CoverLift`. The section signs of a
composite are the products of the section signs along the way
(`Matrix.SignCover.sectionSign_comp`). Over the identity of the lattice, `s_φ` is a character, so
such a `φ` is the identity as soon as `s_φ` is trivial on a spanning set
(`Matrix.SignCover.eq_id_of_sectionSign_eq_one`).

## Main definitions

* `Matrix.SignCover.sectionSign φ a`: the sign `s_φ(a)` of `φ (1, a)`.

## Main results

* `Matrix.SignCover.apply_canonicalSection`: `φ (1, a) = s_φ(a) (1, g a)` for compatible `φ`.
* `Matrix.SignCover.negOnePow_orderedSignForm_mul_sectionSign_add`: the coboundary identity.
* `Matrix.SignCover.sectionSign_zero`, `Matrix.SignCover.sectionSign_id`,
  `Matrix.SignCover.sectionSign_comp`: normalization and functoriality.
* `Matrix.SignCover.sectionSign_add_of_right_eq`: over the identity, the section sign is a
  character of the lattice.
* `Matrix.SignCover.eq_id_of_sectionSign_eq_one`: over the identity, section sign `1` on a
  spanning set forces `φ` to be the identity.
* `Matrix.SignCover.sectionSign_reindex`: the section signs of the relabelling of the ordered
  sign cover are the inversion signs.

## References

* I. B. Frenkel, J. Lepowsky and A. Meurman, *Vertex operator algebras and the Monster*, Academic
  Press (1988), §5.4, for automorphisms of the central extension of a lattice lying over lattice
  isometries.
-/

public section

namespace Matrix.SignCover

open TauCeti

attribute [local instance] trivialMulDistribMulAction

variable {I J K : Type*} [Fintype I] [LinearOrder I] [Fintype J] [LinearOrder J] [Fintype K]
  [LinearOrder K] {B : Matrix I I ℤ} {B' : Matrix J J ℤ} {B'' : Matrix K K ℤ}

/-- **The section sign** `s_φ(a)` of a homomorphism `φ` of ordered sign covers at a lattice vector
`a`: the sign of the image `φ (1, a)` of the canonical lift of `a`. When `φ` fixes the kernel
`ℤˣ` and lies over a linear map `g`, it is the sign with `φ (1, a) = s_φ(a) (1, g a)`
(`Matrix.SignCover.apply_canonicalSection`). -/
noncomputable def sectionSign (φ : SignCover B →* SignCover B') (a : I → ℤ) : ℤˣ :=
  (φ ((signFactorSet B).canonicalSection (.ofAdd a))).left

theorem sectionSign_def (φ : SignCover B →* SignCover B') (a : I → ℤ) :
    sectionSign φ a = (φ ((signFactorSet B).canonicalSection (.ofAdd a))).left :=
  (rfl)

/-- **The image of a canonical lift.** A homomorphism `φ` of ordered sign covers lying over a
linear map `g` sends the canonical lift `(1, a)` to `s_φ(a) (1, g a)`. -/
theorem apply_canonicalSection (φ : SignCover B →* SignCover B') {g : (I → ℤ) →ₗ[ℤ] (J → ℤ)}
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (a : I → ℤ) :
    φ ((signFactorSet B).canonicalSection (.ofAdd a)) =
      FactorSet.inl (signFactorSet B') (sectionSign φ a) *
        (signFactorSet B').canonicalSection (.ofAdd (g a)) := by
  ext
  · simp [sectionSign]
  · simp [hright]

/-- The section sign at the zero vector is `1`. -/
@[simp]
theorem sectionSign_zero (φ : SignCover B →* SignCover B') : sectionSign φ 0 = 1 := by
  rw [sectionSign, ofAdd_zero, FactorSet.canonicalSection_one, map_one,
    FactorSet.Extension.one_left]

/-- The identity has section sign `1`. -/
@[simp]
theorem sectionSign_id (a : I → ℤ) : sectionSign (MonoidHom.id (SignCover B)) a = 1 := by
  simp [sectionSign]

/-- **The coboundary identity of a compatible homomorphism.** If `φ` fixes the kernel `ℤˣ` and
lies over a linear map `g`, its section sign `s_φ` relates the ordered sign `ε` of `B` to the
ordered sign `ε'` of `B'` along `g`:
`ε(a, b) s_φ(a + b) = ε'(g a, g b) s_φ(a) s_φ(b)`. -/
theorem negOnePow_orderedSignForm_mul_sectionSign_add (φ : SignCover B →* SignCover B')
    {g : (I → ℤ) →ₗ[ℤ] (J → ℤ)}
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (a b : I → ℤ) :
    (orderedSignForm B a b).negOnePow * sectionSign φ (a + b) =
      (orderedSignForm B' (g a) (g b)).negOnePow * (sectionSign φ a * sectionSign φ b) := by
  -- In the cover, `(1, a) (1, b) = ε(a, b) (1, a + b)`; compare the signs of the images under `φ`.
  have key := congrArg FactorSet.Extension.left
    (congrArg φ ((signFactorSet B).canonicalSection_mul (.ofAdd a) (.ofAdd b)))
  rw [map_mul, map_mul, hinl, FactorSet.Extension.mul_left, FactorSet.Extension.mul_left,
    ← ofAdd_add] at key
  simp only [FactorSet.inl_right, trivialMulDistribMulAction_smul, signFactorSet_apply,
    orderedSign_apply, toAdd_one, map_zero, LinearMap.zero_apply, Int.negOnePow_zero, mul_one,
    FactorSet.inl_left, hright, FactorSet.canonicalSection_apply, toAdd_ofAdd] at key
  simp only [sectionSign, FactorSet.canonicalSection_apply]
  rw [← key]
  ac_rfl

/-- **The section signs of a composite**: if `φ` lies over `g` and `ψ` fixes the kernel `ℤˣ`, then
`s_(ψ ∘ φ)(a) = s_φ(a) s_ψ(g a)`. -/
theorem sectionSign_comp (ψ : SignCover B' →* SignCover B'') (φ : SignCover B →* SignCover B')
    {g : (I → ℤ) →ₗ[ℤ] (J → ℤ)}
    (hinl : ∀ u, ψ (FactorSet.inl (signFactorSet B') u) = FactorSet.inl (signFactorSet B'') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (a : I → ℤ) :
    sectionSign (ψ.comp φ) a = sectionSign φ a * sectionSign ψ (g a) := by
  rw [sectionSign, MonoidHom.comp_apply, apply_canonicalSection φ hright, map_mul, hinl,
    FactorSet.Extension.mul_left]
  simp [sectionSign]

/-- **Over the identity, the section sign is a character.** If an endomorphism `φ` of an ordered
sign cover fixes the kernel `ℤˣ` and lies over the identity of the lattice, then
`s_φ(a + b) = s_φ(a) s_φ(b)`. -/
theorem sectionSign_add_of_right_eq {φ : SignCover B →* SignCover B}
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B) u)
    (hright : ∀ x, (φ x).right = x.right) (a b : I → ℤ) :
    sectionSign φ (a + b) = sectionSign φ a * sectionSign φ b := by
  have key := negOnePow_orderedSignForm_mul_sectionSign_add φ (g := LinearMap.id) hinl
    (fun x => by rw [hright, LinearMap.id_apply, ofAdd_toAdd]) a b
  rwa [LinearMap.id_apply, LinearMap.id_apply, mul_right_inj] at key

/-- **Trivial section signs on a spanning set force the identity.** If an endomorphism `φ` of an
ordered sign cover fixes the kernel `ℤˣ`, lies over the identity of the lattice, and has section
sign `1` on a set of vectors spanning the lattice, then `φ` is the identity. -/
theorem eq_id_of_sectionSign_eq_one {φ : SignCover B →* SignCover B}
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B) u)
    (hright : ∀ x, (φ x).right = x.right) {S : Set (I → ℤ)}
    (hS : Submodule.span ℤ S = ⊤) (hs : ∀ a ∈ S, sectionSign φ a = 1) :
    φ = MonoidHom.id _ := by
  -- Over the identity, `a ↦ s_φ(a)` is a character of the lattice; it is trivial on a spanning
  -- set, hence everywhere.
  let χ : (I → ℤ) →+ Additive ℤˣ :=
    { toFun a := .ofMul (sectionSign φ a)
      map_zero' := by simp
      map_add' a b := by simp [sectionSign_add_of_right_eq hinl hright a b] }
  have hχ : Submodule.span ℤ S ≤ LinearMap.ker χ.toIntLinearMap :=
    Submodule.span_le.2 fun a ha => by simp [χ, hs a ha]
  rw [hS, top_le_iff, LinearMap.ker_eq_top] at hχ
  have hone (a : I → ℤ) : sectionSign φ a = 1 := by
    simpa [χ] using congr($hχ a)
  refine MonoidHom.ext fun x => ?_
  have h := apply_canonicalSection φ (g := LinearMap.id)
    (fun y => by rw [hright, LinearMap.id_apply, ofAdd_toAdd]) x.right.toAdd
  rw [ofAdd_toAdd, hone, map_one, one_mul, LinearMap.id_apply, ofAdd_toAdd] at h
  rw [← FactorSet.inl_mul_canonicalSection (signFactorSet B) x, map_mul, hinl, h,
    MonoidHom.id_apply]

section Reindex

variable (e : I ≃ J) (hB : B.IsSymm) (he : B.reindex e e = B')

/-- The section signs of the relabelled sign cover are the inversion signs. -/
@[simp]
theorem sectionSign_reindex (a : I → ℤ) :
    sectionSign (reindex e hB he : SignCover B →* SignCover B') a = inversionSign B e a := by
  simp [sectionSign_def]

end Reindex

end Matrix.SignCover
