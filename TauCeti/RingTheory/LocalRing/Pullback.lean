/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Units of a fibre product of rings

For ring homomorphisms `f : R →+* T` and `g : S →+* T`, Mathlib's `RingHom.pullback f g` is the
fibre product `R ×_T S`, the subring of pairs `(r, s)` of `R × S` with `f r = g s`. Its units are
the pairs of units `(u₁, u₂)` of `R` and `S` whose images in `Tˣ` agree:

```text
(R ×_T S)ˣ ≃* Rˣ ×_{Tˣ} Sˣ,   u ↦ (p₁(u), p₂(u)),
```

where `p₁` and `p₂` are the two projections and the fibre product on the right is the equalizer
of the two maps `Rˣ × Sˣ → Tˣ`. No surjectivity of `f` or `g` is needed. This refines Mathlib's
`RingHom.isUnit_pullback_mk_iff`, which says that a pair is a unit exactly when both components
are units.

## Main definitions

* `RingHom.pullbackUnitsEquiv f g`: the group isomorphism of `(R ×_T S)ˣ` with the fibre product
  subgroup of `Rˣ × Sˣ`.

## Main results

* `RingHom.coe_pullbackUnitsEquiv_apply_fst`, `RingHom.coe_pullbackUnitsEquiv_apply_snd`: the
  isomorphism sends a unit to its two projections.
* `RingHom.unitsMap_pullbackFst_pullbackUnitsEquiv_symm`,
  `RingHom.unitsMap_pullbackSnd_pullbackUnitsEquiv_symm`: the unit glued from a compatible pair
  projects to its two components.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §2.
-/

public section

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T)

/-- **Units of a fibre product.** `(R ×_T S)ˣ` is isomorphic to the subgroup of pairs `(u₁, u₂)`
in `Rˣ × Sˣ` whose images in `Tˣ` agree, by sending a unit to its two projections. -/
def pullbackUnitsEquiv :
    (f.pullback g)ˣ ≃*
      ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
        ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ)) where
  toFun u := ⟨(Units.map (f.pullbackFst g : f.pullback g →* R) u,
      Units.map (f.pullbackSnd g : f.pullback g →* S) u),
    Units.ext (u : f.pullback g).property⟩
  invFun v :=
    { val := ⟨((v.val.1 : R), (v.val.2 : S)), congrArg Units.val v.property⟩
      inv := ⟨(((v.val.1⁻¹ : Rˣ) : R), ((v.val.2⁻¹ : Sˣ) : S)), by
        have h := congrArg Inv.inv v.property
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_inv] at h
        exact congrArg Units.val h⟩
      val_inv := Subtype.ext (Prod.ext v.val.1.mul_inv v.val.2.mul_inv)
      inv_val := Subtype.ext (Prod.ext v.val.1.inv_mul v.val.2.inv_mul) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' u v := Subtype.ext (Prod.ext (map_mul _ u v) (map_mul _ u v))

/-- The first component of `pullbackUnitsEquiv` is the first projection. -/
@[simp]
theorem coe_pullbackUnitsEquiv_apply_fst (u : (f.pullback g)ˣ) :
    ((pullbackUnitsEquiv f g u : Rˣ × Sˣ).1 : Rˣ) =
      Units.map (f.pullbackFst g : f.pullback g →* R) u :=
  (rfl)

/-- The second component of `pullbackUnitsEquiv` is the second projection. -/
@[simp]
theorem coe_pullbackUnitsEquiv_apply_snd (u : (f.pullback g)ˣ) :
    ((pullbackUnitsEquiv f g u : Rˣ × Sˣ).2 : Sˣ) =
      Units.map (f.pullbackSnd g : f.pullback g →* S) u :=
  (rfl)

/-- The unit of `R ×_T S` glued from a compatible pair `(u₁, u₂)` projects to `u₁` in `R`. -/
@[simp]
theorem unitsMap_pullbackFst_pullbackUnitsEquiv_symm
    (v : ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
      ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ))) :
    Units.map (f.pullbackFst g : f.pullback g →* R) ((pullbackUnitsEquiv f g).symm v) =
      v.val.1 :=
  (rfl)

/-- The unit of `R ×_T S` glued from a compatible pair `(u₁, u₂)` projects to `u₂` in `S`. -/
@[simp]
theorem unitsMap_pullbackSnd_pullbackUnitsEquiv_symm
    (v : ((Units.map (f : R →* T)).comp (MonoidHom.fst Rˣ Sˣ)).eqLocus
      ((Units.map (g : S →* T)).comp (MonoidHom.snd Rˣ Sˣ))) :
    Units.map (f.pullbackSnd g : f.pullback g →* S) ((pullbackUnitsEquiv f g).symm v) =
      v.val.2 :=
  (rfl)

end RingHom
