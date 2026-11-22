/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.ExactSequence
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Twist

/-!
# The fibres of `H¹(G, A) → H¹(G, A'')` over an arbitrary class

Let `1 → A' → A → A'' → 1` be a short exact sequence of topological `G`-groups given by
`i : A' →ₜ* A` and `p : A →ₜ* A''` (`TauCeti.NonabelianH1.IsGroupExtension`). The neutral fibre of
`H¹(G, A) → H¹(G, A'')` is the quotient of `H¹(G, A')` by the action of `A''ᴳ`
(`TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientEquiv`). This file describes every other
fibre by twisting.

Let `c` be a continuous cocycle of `G` with values in `A`. The map `p` induces a map
`₍c₎A → ₍p ∘ c₎A''` of twisted groups, and its kernel `₍c₎A'` is a `G`-stable subgroup of `₍c₎A`
(`TauCeti.NonabelianH1.Twist.ker`). As a topological group it is `A'`, via `i`
(`TauCeti.NonabelianH1.IsGroupExtension.twistKerEquiv`), with `g : G` acting on `A'` by
`x ↦ c g * g • x * (c g)⁻¹`, computed inside `A`: the twist of `A'` by `c`, which is defined
although `c` need not take values in `A'`. The twisted sequence

`1 → ₍c₎A' → ₍c₎A → ₍p ∘ c₎A'' → 1`

is again a short exact sequence of topological `G`-groups
(`TauCeti.NonabelianH1.IsGroupExtension.twist`). The twisting bijection `H¹(G, ₍c₎A) ≃ H¹(G, A)`
carries the neutral fibre of the twisted sequence onto the fibre of `H¹(G, A) → H¹(G, A'')` over
the class of `p ∘ c`. Hence that fibre is the quotient of `H¹(G, ₍c₎A')` by the action of
`(₍p ∘ c₎A'')ᴳ` (`TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientTwistEquiv`). Every class of
`H¹(G, A'')` with nonempty fibre is the class of some `p ∘ c`, so this describes all the fibres.

As a consequence, `H¹(G, A) → H¹(G, A'')` is injective exactly when, for every cocycle `c` of
`A`, the map `H¹(G, ₍c₎A') → H¹(G, ₍c₎A)` is constant at the base point
(`TauCeti.NonabelianH1.IsGroupExtension.map_injective_iff`).

## Main definitions

* `TauCeti.NonabelianH1.IsGroupExtension.twistKerEquiv`: the identification `A' ≃ₜ* ₍c₎A'`
  given by `i`.
* `TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientTwistEquiv`: the bijection from the
  quotient of `H¹(G, ₍c₎A')` by `(₍p ∘ c₎A'')ᴳ` onto the fibre over the class of `p ∘ c`.

## Main results

* `TauCeti.NonabelianH1.IsGroupExtension.twist`: twisting by a cocycle of `A` preserves short
  exact sequences.
* `TauCeti.NonabelianH1.IsGroupExtension.map_eq_mk_map_iff_mem_range`: a class of `H¹(G, A)`
  lies over the class of `p ∘ c` exactly when it comes from `H¹(G, ₍c₎A')` under the twisting
  bijection.
* `TauCeti.NonabelianH1.IsGroupExtension.map_injective_iff`: the injectivity criterion.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.5.5: the fibres of `H¹(G, B) → H¹(G, C)`
  for a normal subgroup `A` of `B` with quotient `C`, described by twisting.
-/

public section

open Topology

namespace TauCeti

namespace NonabelianH1

variable {G A' A A'' : Type*} [Group G] [TopologicalSpace G]
  [Group A'] [TopologicalSpace A'] [MulDistribMulAction G A']
  [Group A] [TopologicalSpace A] [MulDistribMulAction G A]
  [Group A''] [TopologicalSpace A''] [MulDistribMulAction G A'']

namespace IsGroupExtension

variable {i : A' →ₜ* A} {p : A →ₜ* A''} (hE : IsGroupExtension G i p)

include hE

/-- **Twisting preserves short exact sequences**: for a cocycle `c` of `A`, the twisted kernel
`₍c₎A'`, the twist `₍c₎A` and the twist `₍p ∘ c₎A''` form a short exact sequence of topological
`G`-groups. -/
theorem twist (c : Cocycle G A) :
    IsGroupExtension G (ContinuousMonoidHom.subgroupSubtype (Twist.ker c p hE.compatible_right))
      (Twist.map c (ContinuousMonoidHom.id G) p hE.compatible_right) where
  map_smul_left _ _ := (rfl)
  map_smul_right := Twist.map_smul (ContinuousMonoidHom.id G) p hE.compatible_right
  isEmbedding := IsEmbedding.subtypeVal
  surjective x := by
    obtain ⟨a, ha⟩ := hE.surjective x.toOriginal
    exact ⟨Twist.ofOriginal a, Twist.ext (by simp [ha])⟩
  mulExact x := Twist.map_eq_one_iff_mem_ker.trans
    ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩

/-- An element of `A'` gives an element of the twisted kernel `₍c₎A'` through `i`. -/
private def toTwistKer (c : Cocycle G A) : A' →ₜ* Twist.ker c p hE.compatible_right where
  toFun a := ⟨Twist.ofOriginal (i a), Twist.mem_ker.mpr (hE.mulExact.apply_apply_eq_one a)⟩
  map_one' := Subtype.ext <| Twist.ext (_root_.map_one i)
  map_mul' a b := Subtype.ext <| Twist.ext (_root_.map_mul i a b)
  continuous_toFun := by fun_prop

private theorem isEmbedding_toTwistKer (c : Cocycle G A) : IsEmbedding (hE.toTwistKer c) :=
  .of_comp (map_continuous _) (Twist.continuous_toOriginal.comp continuous_subtypeVal)
    hE.isEmbedding

private theorem surjective_toTwistKer (c : Cocycle G A) : Function.Surjective (hE.toTwistKer c) :=
  fun x ↦
    have ⟨a, ha⟩ := (hE.mulExact x.val.toOriginal).mp (Twist.mem_ker.mp x.property)
    ⟨a, Subtype.ext <| Twist.ext ha⟩

/-- The **twisted kernel is `A'`**: the map `i` identifies `A'` with the twisted kernel `₍c₎A'` as
a topological group (`TauCeti.NonabelianH1.IsGroupExtension.toOriginal_twistKerEquiv`). It need
not be `G`-equivariant: it carries the action on `₍c₎A'` to `x ↦ c g * g • x * (c g)⁻¹`, computed
inside `A` (`TauCeti.NonabelianH1.IsGroupExtension.apply_twistKerEquiv_symm_smul`). -/
noncomputable def twistKerEquiv (c : Cocycle G A) : A' ≃ₜ* Twist.ker c p hE.compatible_right :=
  .mk' ((hE.isEmbedding_toTwistKer c).toHomeomorphOfSurjective (hE.surjective_toTwistKer c))
    (map_mul (hE.toTwistKer c))

/-- The element of `₍c₎A'` corresponding to `a : A'` has underlying element `i a` of `A`. -/
@[simp]
theorem toOriginal_twistKerEquiv (c : Cocycle G A) (a : A') :
    ((hE.twistKerEquiv c a : Twist c)).toOriginal = i a :=
  (rfl)

/-- An element `x` of `₍c₎A'` has underlying element `i (e⁻¹ x)` of `A`, for `e` the identification
`TauCeti.NonabelianH1.IsGroupExtension.twistKerEquiv`. -/
@[simp]
theorem apply_twistKerEquiv_symm (c : Cocycle G A) (x : Twist.ker c p hE.compatible_right) :
    i ((hE.twistKerEquiv c).symm x) = (x : Twist c).toOriginal := by
  conv_rhs => rw [← (hE.twistKerEquiv c).apply_symm_apply x, toOriginal_twistKerEquiv]

/-- Through `i`, the action of `G` on `₍c₎A'` is the twisted action
`x ↦ c g * g • x * (c g)⁻¹`, computed inside `A`. -/
theorem apply_twistKerEquiv_symm_smul (c : Cocycle G A) (g : G)
    (x : Twist.ker c p hE.compatible_right) :
    i ((hE.twistKerEquiv c).symm (g • x)) =
      c g * g • i ((hE.twistKerEquiv c).symm x) * (c g)⁻¹ := by
  simp

variable [IsTopologicalGroup A] [ContinuousSMul G A]

/-- **The fibre over the class of `p ∘ c`**: a class of `H¹(G, A)` maps to the class of `p ∘ c` in
`H¹(G, A'')` exactly when it is the image, under the twisting bijection
`H¹(G, ₍c₎A) ≃ H¹(G, A)`, of a class of `H¹(G, ₍c₎A')`. -/
theorem map_eq_mk_map_iff_mem_range (c : Cocycle G A) {x : NonabelianH1 G A} :
    map (ContinuousMonoidHom.id G) p hE.compatible_right x =
        NonabelianH1.mk (c.map (ContinuousMonoidHom.id G) p hE.compatible_right) ↔
      x ∈ Set.range (ofTwistEquiv c ∘
        map (ContinuousMonoidHom.id G) _ (hE.twist c).compatible_left) := by
  constructor
  · induction x using induction_on with | mk f =>
    -- If `p ∘ c` is the twist of `p ∘ f` by `p b`, then `f` twisted by `b` lies over `p ∘ c`
    -- pointwise, so it differs from `c` by a cocycle of `₍c₎A` with values in `₍c₎A'`.
    rw [map_mk, mk_eq_mk_iff]
    rintro ⟨a, ha⟩
    obtain ⟨b, rfl⟩ := hE.surjective a
    have hmem (g : G) : c.ofTwistEquiv.symm (f.twist b) g ∈
        Set.range (ContinuousMonoidHom.subgroupSubtype (Twist.ker c p hE.compatible_right)) := by
      have hpc : p (c g) = (p b)⁻¹ * p (f g) * g • p b := by
        simpa only [Cocycle.map_apply, ContinuousMonoidHom.id_toFun] using ha g
      refine ⟨⟨c.ofTwistEquiv.symm (f.twist b) g, Twist.mem_ker.mpr ?_⟩, rfl⟩
      simp [hpc, hE.map_smul_right]
    refine ⟨NonabelianH1.mk ((c.ofTwistEquiv.symm (f.twist b)).liftOfMemRange _
      (hE.twist c).isEmbedding (hE.twist c).compatible_left hmem), ?_⟩
    rw [Function.comp_apply, map_mk, Cocycle.map_liftOfMemRange, ofTwistEquiv_mk,
      Equiv.apply_symm_apply, mk_twist]
  · rintro ⟨y, rfl⟩
    induction y using induction_on with | mk d =>
    simp only [Function.comp_apply, map_mk, ofTwistEquiv_mk]
    refine congrArg NonabelianH1.mk <| Cocycle.ext fun g ↦ ?_
    simp [Twist.mem_ker.mp (d g).property]

/-- **The fibres of `H¹(G, A) → H¹(G, A'')` by twisting**: for a cocycle `c` of `A`, twisting
identifies the quotient of `H¹(G, ₍c₎A')` by the action of `(₍p ∘ c₎A'')ᴳ` with the fibre of
`H¹(G, A) → H¹(G, A'')` over the class of `p ∘ c`. The action is that of the twisted short exact
sequence `TauCeti.NonabelianH1.IsGroupExtension.twist`. For the trivial cocycle this is the
description of the neutral fibre `TauCeti.NonabelianH1.IsGroupExtension.orbitRelQuotientEquiv`. -/
noncomputable def orbitRelQuotientTwistEquiv (c : Cocycle G A) :
    letI := (hE.twist c).mulAction
    MulAction.orbitRel.Quotient
        (FixedPoints.subgroup G (Twist (c.map (ContinuousMonoidHom.id G) p hE.compatible_right)))
        (NonabelianH1 G (Twist.ker c p hE.compatible_right)) ≃
      {x : NonabelianH1 G A // map (ContinuousMonoidHom.id G) p hE.compatible_right x =
        NonabelianH1.mk (c.map (ContinuousMonoidHom.id G) p hE.compatible_right)} :=
  (hE.twist c).orbitRelQuotientEquiv.trans <| (ofTwistEquiv c).subtypeEquiv fun x ↦ by
    rw [hE.map_eq_mk_map_iff_mem_range, (hE.twist c).map_eq_one_iff_mem_range_map, Set.range_comp,
      (ofTwistEquiv c).injective.mem_set_image]

/-- The orbit of a class `y` of `H¹(G, ₍c₎A')` goes to the twist by `c` of its image in
`H¹(G, ₍c₎A)`. -/
@[simp]
theorem coe_orbitRelQuotientTwistEquiv_mk (c : Cocycle G A)
    (y : NonabelianH1 G (Twist.ker c p hE.compatible_right)) :
    (hE.orbitRelQuotientTwistEquiv c (Quotient.mk _ y) : NonabelianH1 G A) =
      ofTwistEquiv c (map (ContinuousMonoidHom.id G) _ (hE.twist c).compatible_left y) := by
  simp [orbitRelQuotientTwistEquiv]

/-- **Injectivity criterion**: `H¹(G, A) → H¹(G, A'')` is injective exactly when, for every
cocycle `c` of `A`, every class of `H¹(G, ₍c₎A')` maps to the base point of `H¹(G, ₍c₎A)`. -/
theorem map_injective_iff :
    Function.Injective (map (ContinuousMonoidHom.id G) p hE.compatible_right) ↔
      ∀ (c : Cocycle G A) (y : NonabelianH1 G (Twist.ker c p hE.compatible_right)),
        map (ContinuousMonoidHom.id G) _ (hE.twist c).compatible_left y = 1 := by
  constructor
  · intro hinj c y
    rw [← (ofTwistEquiv c).apply_eq_iff_eq, ofTwistEquiv_one]
    refine hinj (((hE.map_eq_mk_map_iff_mem_range c).mpr ⟨y, rfl⟩).trans ?_)
    rw [map_mk]
  · intro h x x' hxx'
    induction x using induction_on with | mk c =>
    rw [map_mk, eq_comm, hE.map_eq_mk_map_iff_mem_range c] at hxx'
    obtain ⟨y, rfl⟩ := hxx'
    simp [h c y]

end IsGroupExtension

end NonabelianH1

end TauCeti
