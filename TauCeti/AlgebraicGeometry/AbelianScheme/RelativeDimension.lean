/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.PureRelativeDimension
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# The relative dimension of an abelian scheme

The **relative dimension** of an abelian scheme `A` over `S` is the function `S → ℕ` sending a
point `s` to the dimension of the fibre `A_s`. It is a locally constant function, not a number:
on a disconnected base the fibres over different components may have different dimensions. An
abelian scheme is smooth of relative dimension `g` in Mathlib's sense
(`SmoothOfRelativeDimension g`) exactly when this function is constantly `g`.

Local constancy needs neither properness nor the group law. The structure morphism is smooth with
geometrically connected fibres, so its fibres are smooth and connected, hence irreducible, schemes
over the residue fields. Near each point of `A` the structure morphism is smooth of some relative
dimension `n`; every fibre meeting that open neighbourhood is irreducible with a nonempty open
part of pure dimension `n`, hence has dimension `n`. Since smooth morphisms are open, the fibres
over an open neighbourhood of each point of `S` all have the same dimension
(`TauCeti.AlgebraicGeometry.isLocallyConstant_topologicalKrullDim_fiber`).

The relative dimension is pulled back by base change, since the fibre of `A_T` over `t` is the
base change of the fibre of `A` over the image of `t` along an extension of residue fields. It is
zero for the identity abelian scheme, and it only depends on the underlying scheme over `S`.

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension`: the function `s ↦ dim A_s`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.topologicalKrullDim_fiber`: the fibre over `s` has
  Krull dimension `A.relativeDimension s`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.isLocallyConstant_relativeDimension`: the relative
  dimension is locally constant.
* `TauCeti.AlgebraicGeometry.AbelianScheme.smoothOfRelativeDimension_iff`: `A` is smooth of
  relative dimension `n` over `S` exactly when its relative dimension is constantly `n`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_baseChange`: for `f : T ⟶ S`, the
  relative dimension of `A_T` at `t` is that of `A` at `f t`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_identity`: the identity abelian
  scheme has relative dimension zero.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_eq_of_iso`: abelian schemes with
  isomorphic underlying schemes over `S` have the same relative dimension.

## References

* G. Faltings and C.-L. Chai, *Degeneration of abelian varieties*, Chapter I, §1.
* J. S. Milne, *Abelian varieties* (2022 revision), §20.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianScheme

universe u

variable {S T : Scheme.{u}}

/-- The **relative dimension** of an abelian scheme `A` over `S` at a point `s : S`: the Krull
dimension of the fibre `A_s` (`topologicalKrullDim_fiber`). It is a locally constant function of
`s` (`isLocallyConstant_relativeDimension`). -/
noncomputable def relativeDimension (A : AbelianScheme S) (s : S) : ℕ :=
  ((topologicalKrullDim (A.toOver.hom.fiber s)).unbotD 0).toNat

/-- The fibre of an abelian scheme `A` over `s` has Krull dimension `A.relativeDimension s`. -/
@[simp]
theorem topologicalKrullDim_fiber (A : AbelianScheme S) (s : S) :
    topologicalKrullDim (A.toOver.hom.fiber s) = A.relativeDimension s := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_fiber_eq_natCast A.toOver.hom s
  simp [relativeDimension, hn]

/-- The relative dimension of an abelian scheme is a locally constant function on the base. -/
theorem isLocallyConstant_relativeDimension (A : AbelianScheme S) :
    IsLocallyConstant A.relativeDimension :=
  (isLocallyConstant_topologicalKrullDim_fiber A.toOver.hom).comp fun d ↦ (d.unbotD 0).toNat

/-- An abelian scheme is smooth of relative dimension `n` over its base exactly when its relative
dimension is constantly `n`. -/
theorem smoothOfRelativeDimension_iff (A : AbelianScheme S) (n : ℕ) :
    SmoothOfRelativeDimension n A.toOver.hom ↔ ∀ s, A.relativeDimension s = n := by
  simp only [smoothOfRelativeDimension_iff_forall_topologicalKrullDim_fiber_eq,
    topologicalKrullDim_fiber, Nat.cast_inj]

/-- The relative dimension of the base change of `A` along `f : T ⟶ S` at `t` is the relative
dimension of `A` at `f t`. -/
@[simp]
theorem relativeDimension_baseChange (A : AbelianScheme S) (f : T ⟶ S) (t : T) :
    (A.baseChange f).relativeDimension t = A.relativeDimension (f t) := by
  -- The structure morphism of `A_T` is the base change `pullback.snd` of that of `A`.
  have h : topologicalKrullDim ((A.baseChange f).toOver.hom.fiber t) =
      topologicalKrullDim (A.toOver.hom.fiber (f t)) :=
    topologicalKrullDim_fiber_of_isPullback (IsPullback.of_hasPullback A.toOver.hom f) t
  rw [topologicalKrullDim_fiber, topologicalKrullDim_fiber] at h
  exact_mod_cast h

/-- The identity abelian scheme has relative dimension zero. -/
@[simp]
theorem relativeDimension_identity (s : S) : (identity S).relativeDimension s = 0 := by
  -- The structure morphism of the identity abelian scheme is `𝟙 S`, an open immersion.
  have : SmoothOfRelativeDimension 0 (identity S).toOver.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 S))
  exact ((identity S).smoothOfRelativeDimension_iff 0).mp this s

/-- Abelian schemes whose underlying schemes over `S` are isomorphic have the same relative
dimension. The isomorphism need not respect the group laws; an isomorphism `e : A ≅ B` of abelian
schemes supplies one as `toOverFunctor.mapIso e`. -/
theorem relativeDimension_eq_of_iso {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) :
    A.relativeDimension = B.relativeDimension := by
  funext s
  -- An isomorphism over `S` is a cartesian square along `𝟙 S`.
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have h : topologicalKrullDim (A.toOver.hom.fiber s) =
      topologicalKrullDim (B.toOver.hom.fiber s) :=
    topologicalKrullDim_fiber_of_isPullback
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 S) ⟨by simp⟩) s
  rw [topologicalKrullDim_fiber, topologicalKrullDim_fiber] at h
  exact_mod_cast h

end AbelianScheme

end AlgebraicGeometry

end TauCeti
