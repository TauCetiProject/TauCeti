/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt

/-!
# The free pro-`p` group on one generator is `ℤ_p`

The free pro-`p` group on a one-element type and the additive group of the `p`-adic integers
represent the same functor on pro-`p` groups: a continuous homomorphism out of either into a
pro-`p` group `P` is the same thing as an element of `P`, the image of the generator. For the
free group this is its universal property; for `ℤ_[p]` it is the `p`-adic power
`TauCeti.IsProP.padicPowHom`. The two universal properties assemble into a topological group
isomorphism `freeProP p X ≃ₜ* Multiplicative ℤ_[p]` carrying the generator to `1`, whose inverse
sends `l` to the `p`-adic power of the generator by `l`.

The free pro-`p` group on one generator is therefore topologically finitely generated of rank
one. No product decomposition of the profinite integers is involved.

The generating type is taken in `Type`, the universe of `ℤ_[p]`, because the universal property
of `freeProP p X` only produces homomorphisms into pro-`p` groups of the universe of `X`.

## Main definitions

* `TauCeti.freeProP.equivPadicInt`: the isomorphism `freeProP p X ≃ₜ* Multiplicative ℤ_[p]`
  for a one-element type `X`.

## Main results

* `TauCeti.freeProP.equivPadicInt_of`, `TauCeti.freeProP.equivPadicInt_symm_ofAdd`: the
  isomorphism carries the generator to `1`, and its inverse is the `p`-adic power of the
  generator.
* `TauCeti.topologicalGeneratorRank_freeProP_of_unique`: the free pro-`p` group on one generator
  has topological generator rank one.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 3.3 and 4.3.
-/

public section

namespace TauCeti

namespace freeProP

variable (p : ℕ) [Fact p.Prime] (X : Type) [Unique X]

/-- **The free pro-`p` group on one generator is `ℤ_p`.** The topological group isomorphism
from `freeProP p X`, for a one-element type `X`, to the additive group of the `p`-adic integers,
sending the generator to `1`. Its inverse sends `l` to the `p`-adic power of the generator
by `l`. -/
noncomputable def equivPadicInt : freeProP p X ≃ₜ* Multiplicative ℤ_[p] where
  toFun := lift (isProP_multiplicative_padicInt p) fun _ ↦ Multiplicative.ofAdd 1
  invFun := (isProP_freeProP p X).padicPowHom (of default)
  left_inv x := by
    have h : ((isProP_freeProP p X).padicPowHom (of default)).comp
        (lift (isProP_multiplicative_padicInt p) fun _ ↦ Multiplicative.ofAdd (1 : ℤ_[p])) =
          ContinuousMonoidHom.id (freeProP p X) :=
      hom_ext fun x ↦ by simp [Unique.eq_default x]
    exact DFunLike.congr_fun h x
  right_inv l := by
    have h : (lift (isProP_multiplicative_padicInt p)
        fun _ : X ↦ Multiplicative.ofAdd (1 : ℤ_[p])).comp
          ((isProP_freeProP p X).padicPowHom (of default)) =
            ContinuousMonoidHom.id (Multiplicative ℤ_[p]) :=
      continuousMonoidHom_ext_multiplicative_padicInt (by simp)
    exact DFunLike.congr_fun h l
  map_mul' := map_mul _
  continuous_toFun := (lift (isProP_multiplicative_padicInt p) _).continuous
  continuous_invFun := ((isProP_freeProP p X).padicPowHom (of default)).continuous

/-- The isomorphism with `ℤ_p` is the lift of the map sending the generator to `1`. -/
@[simp]
theorem coe_equivPadicInt :
    (equivPadicInt p X : freeProP p X →ₜ* Multiplicative ℤ_[p]) =
      lift (isProP_multiplicative_padicInt p) fun _ ↦ Multiplicative.ofAdd 1 :=
  (rfl)

/-- The isomorphism with `ℤ_p` sends the generator to `1`. -/
@[simp]
theorem equivPadicInt_of (x : X) :
    equivPadicInt p X (of x) = Multiplicative.ofAdd (1 : ℤ_[p]) :=
  lift_of _ _ x

/-- The inverse of the isomorphism with `ℤ_p` is the `p`-adic power homomorphism of the
generator. -/
@[simp]
theorem coe_equivPadicInt_symm :
    ((equivPadicInt p X).symm : Multiplicative ℤ_[p] →ₜ* freeProP p X) =
      (isProP_freeProP p X).padicPowHom (of default) :=
  (rfl)

/-- The inverse of the isomorphism with `ℤ_p` sends `l` to the `p`-adic power of the generator
by `l`. -/
@[simp]
theorem equivPadicInt_symm_ofAdd (l : ℤ_[p]) :
    (equivPadicInt p X).symm (Multiplicative.ofAdd l) =
      (isProP_freeProP p X).padicPow (of default) l := by
  have h := DFunLike.congr_fun (coe_equivPadicInt_symm p X) (Multiplicative.ofAdd l)
  simp only [ContinuousMonoidHom.coe_coe, IsProP.padicPowHom_apply, toAdd_ofAdd] at h
  exact h

/-- The isomorphism with `ℤ_p` is the unique topological isomorphism carrying the generator
to `1`. -/
theorem equivPadicInt_unique (e : freeProP p X ≃ₜ* Multiplicative ℤ_[p])
    (he : ∀ x : X, e (of x) = Multiplicative.ofAdd 1) : e = equivPadicInt p X := by
  have h : (e : freeProP p X →ₜ* Multiplicative ℤ_[p]) =
      (equivPadicInt p X : freeProP p X →ₜ* Multiplicative ℤ_[p]) :=
    hom_ext fun x ↦ by simp [he x]
  exact ContinuousMulEquiv.ext fun x ↦ DFunLike.congr_fun h x

end freeProP

variable (p : ℕ) [Fact p.Prime] {X : Type} [Unique X]

/-- The free pro-`p` group on one generator is topologically finitely generated. -/
theorem isTopologicallyFinitelyGenerated_freeProP_of_unique :
    IsTopologicallyFinitelyGenerated (freeProP p X) :=
  (isTopologicallyFinitelyGenerated_congr (freeProP.equivPadicInt p X)).mpr
    (isTopologicallyFinitelyGenerated_multiplicative_padicInt p)

/-- The free pro-`p` group on one generator has topological generator rank one. -/
@[simp]
theorem topologicalGeneratorRank_freeProP_of_unique :
    topologicalGeneratorRank (freeProP p X) = 1 := by
  rw [topologicalGeneratorRank_congr (freeProP.equivPadicInt p X),
    topologicalGeneratorRank_multiplicative_padicInt]

/-- The natural-number topological generator rank of the free pro-`p` group on one generator
is one. -/
@[simp]
theorem topologicalGeneratorRankNat_freeProP_of_unique
    (h : IsTopologicallyFinitelyGenerated (freeProP p X)) :
    topologicalGeneratorRankNat (freeProP p X) h = 1 := by
  have := topologicalGeneratorRankNat_eq_topologicalGeneratorRank h
  rw [topologicalGeneratorRank_freeProP_of_unique] at this
  exact_mod_cast this

end TauCeti
