/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Character
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.ZeroLeft
import TauCeti.RepresentationTheory.Rep.TensorInvariant

/-!
# Cup product with the connecting class of a character, on cocycles

Let `G` be a finite group, `χ : Gᵃᵇ → ℚ/ℤ` a character and `A` a representation of `G` with an
invariant `a ∈ Aᴳ`. Write `χ'(g) ∈ [0, 1)` for the representative of `χ(g)`. This file computes
the cup product `a ∪ δχ ∈ H²(G, A)` of the degree-zero class of `a` with the connecting class
`δχ ∈ H²(G, ℤ)` of `χ` (`TauCeti.TateCohomology.characterConnectingClass`) on cocycles: it is the
class of the carry cocycle

```text
(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • a,
```

with the carry `TauCeti.ContCohomology.characterCarry` of `χ`.

The connecting map of `0 → ℤ → ℚ → ℚ/ℤ → 0` is computed by lifting `χ` to the rational cochain
`χ'`, whose coboundary `(g, h) ↦ χ'(g) + χ'(h) - χ'(gh)` is the carry
(`TauCeti.ContCohomology.intCast_characterCarry`). Cup product with the class of `a` is induced
by the map `ℤ → A`, `1 ↦ a`, which multiplies the carry by `a`.

This is the cocycle description of the classes `a ∪ δχ` in the character formula
`χ(artinMap a) = inv(a ∪ δχ)` of a class formation, valid for every character of every finite
group. For a cyclic group of order `n` and a character sending a generator to `1 / n`, the carry
cocycle is the cocycle of two-periodicity (`TauCeti.ContCohomology.characterCarry_eq_ite`).

## Main definitions

* `TauCeti.groupCohomology.characterCarryCocycles₂`: the carry cocycle
  `(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • a` of a character and an invariant, as a `2`-cocycle of an integral
  representation.

## Main results

* `TauCeti.TateCohomology.characterConnectingClass_eq_H2π`: `δχ` is the class of the integer
  carry cocycle of `χ`.
* `TauCeti.TateCohomology.cup_characterConnectingClass_eq_H2π`: `a ∪ δχ` is the class of the
  carry cocycle of `χ` and `a`.

## References

* J.-P. Serre, *Local Fields*, Chapter XIV, §1.
* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter VII (Tate, *Global
  Class Field Theory*), §1.
-/

public noncomputable section

open CategoryTheory MonoidalCategory groupCohomology

namespace TauCeti.groupCohomology

variable {G : Type} [Group G]

/-- **The carry cocycle** of a character `χ : G → ℚ/ℤ` and an invariant `a` of a representation
`A` of `G`: the `2`-cocycle `(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • a`, where `χ'(x) ∈ [0, 1)` represents
`χ(x)` (`characterCarryCocycles₂_apply`). For a finite group its class is the cup product
`a ∪ δχ` (`TauCeti.TateCohomology.cup_characterConnectingClass_eq_H2π`). -/
def characterCarryCocycles₂ (χ : Additive G →+ AddCircle (1 : ℚ)) (A : Rep ℤ G)
    (a : A.ρ.invariants) : cocycles₂ A :=
  ⟨fun p ↦ ContCohomology.characterCarry χ p.1 p.2 • (a : A),
    (mem_cocycles₂_iff _).2 fun g h j ↦ by
      simp only [map_zsmul, a.2 g, ← add_zsmul, ContCohomology.characterCarry_mul_add]⟩

/-- The value of the carry cocycle of `χ` and `a` at `(g, h)` is the carry of `χ` times `a`. -/
@[simp]
theorem characterCarryCocycles₂_apply (χ : Additive G →+ AddCircle (1 : ℚ)) (A : Rep ℤ G)
    (a : A.ρ.invariants) (g h : G) :
    characterCarryCocycles₂ χ A a (g, h) = ContCohomology.characterCarry χ g h • (a : A) :=
  (rfl)

end TauCeti.groupCohomology

namespace TauCeti.TateCohomology

variable {G : Type} [Group G] [Fintype G]

/-- **The connecting class of a character is its carry class.** For a character `χ` of a finite
group, `δχ ∈ H²(G, ℤ)` is the class of every `2`-cocycle whose value at `(g, h)` is the carry
`⌊χ'(g) + χ'(h)⌋` of `χ`. -/
theorem characterConnectingClass_eq_H2π
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) (c : cocycles₂ (Rep.trivial ℤ G ℤ))
    (hc : ∀ g h, c (g, h) =
      ContCohomology.characterCarry (χ.comp Abelianization.of.toAdditive) g h) :
    characterConnectingClass G χ =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app _ (H2π _ c) := by
  set χ' := χ.comp Abelianization.of.toAdditive
  rw [characterConnectingClass_def, H1IsoOfIsTrivial_inv_apply]
  congr 1
  -- `δχ` is the class of the coboundary of the lift `χ'` of `χ` to `ℚ`, which is the carry. The
  -- closing `rfl` identifies the cocycle produced by `δ₁_apply` with `c` (structure eta for the
  -- subtype of cocycles).
  refine (δ₁_apply (Rep.ratAddCircleShortComplex_shortExact G) _
    (fun g ↦ (AddCircle.equivIco 1 0 (χ' (.ofMul g)) : ℚ)) ?_ (c : G × G → ℤ) ?_).trans rfl
  · funext g
    rw [Function.comp_apply, Rep.ratAddCircleShortComplex_g_hom_apply, AddCircle.coe_equivIco]
    -- The `1`-cocycle of a homomorphism `f : G → ℚ/ℤ` is `f` itself, by definition of
    -- `cocycles₁IsoOfIsTrivial`.
    rfl
  · funext p
    rw [Function.comp_apply, Rep.ratAddCircleShortComplex_f_hom_apply, d₁₂_hom_apply, hc,
      ContCohomology.intCast_characterCarry, Representation.trivial_apply]
    ring

/-- **Cup product with the connecting class of a character is the carry class.** For a character
`χ` of a finite group and an invariant `a` of a representation `A`, the cup product
`a ∪ δχ ∈ H²(G, A ⊗ ℤ) = H²(G, A)` of the degree-zero class of `a` with the connecting class of
`χ` is the class of the carry cocycle `(g, h) ↦ ⌊χ'(g) + χ'(h)⌋ • a`. -/
theorem cup_characterConnectingClass_eq_H2π
    (χ : Additive (Abelianization G) →+ AddCircle (1 : ℚ)) (A : Rep ℤ G) (a : A.ρ.invariants) :
    (tateCohomologyFunctor 2).map (ρ_ A).hom
        (cup A (Rep.trivial ℤ G ℤ) 0 2 2 (zero_add 2) (H0π A a) (characterConnectingClass G χ)) =
      (_root_.TateCohomology.isoGroupCohomology 2).inv.app A
        (H2π A (TauCeti.groupCohomology.characterCarryCocycles₂
          (χ.comp Abelianization.of.toAdditive) A a)) := by
  set χ' := χ.comp Abelianization.of.toAdditive
  -- The carry cocycle of `1 ∈ ℤ` is the integer carry of `χ`.
  set c₁ := TauCeti.groupCohomology.characterCarryCocycles₂ χ' (Rep.trivial ℤ G ℤ)
    ⟨(1 : ℤ), fun _ ↦ rfl⟩
  have hc₁ (g h : G) : c₁ (g, h) = ContCohomology.characterCarry χ' g h := by
    rw [TauCeti.groupCohomology.characterCarryCocycles₂_apply, smul_eq_mul, mul_one]
  rw [cup_zero_left, cup0H_H0π, characterConnectingClass_eq_H2π χ c₁ hc₁,
    ← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc]
  -- Cup product with the class of `a` is induced by `φ : ℤ → A`, `1 ↦ a`, which commutes with the
  -- comparison of Tate and ordinary cohomology and sends the carry class of `1` to that of `a`.
  set φ : Rep.trivial ℤ G ℤ ⟶ A :=
    (Rep.trivial ℤ G ℤ).tensorInvariant a ≫ (β_ (Rep.trivial ℤ G ℤ) A).hom ≫ (ρ_ A).hom with hφ
  have h := ConcreteCategory.congr_hom
    ((_root_.TateCohomology.isoGroupCohomology 2).inv.naturality φ) (H2π _ c₁)
  have hmap : groupCohomology.map (MonoidHom.id G) φ 2 (H2π _ c₁) =
      H2π A (TauCeti.groupCohomology.characterCarryCocycles₂ χ' A a) := by
    rw [H2π_comp_map_apply]
    congr 1
    refine Subtype.ext (funext fun q ↦ ?_)
    have hq : (mapCocycles₂ (MonoidHom.id G) φ c₁ : G × G → A) q =
        TauCeti.groupCohomology.characterCarryCocycles₂ χ' A a q := by
      rw [TauCeti.groupCohomology.mapCocycles₂_apply, hc₁,
        TauCeti.groupCohomology.characterCarryCocycles₂_apply]
      -- The scalar action of `ℤ` on `A` is its module structure, which agrees with `zsmul`.
      exact (TauCeti.Rep.tensorInvariant_braiding_rightUnitor_hom_apply a _).trans
        (int_smul_eq_zsmul _ _ _)
    exact hq
  refine h.symm.trans ?_
  rw [← hmap]
  -- The left side evaluates a composite of morphisms, and the functor `groupCohomology.functor`
  -- acts on `φ` by `groupCohomology.map (MonoidHom.id G) φ` by definition. `ModuleCat.comp_apply`
  -- cannot be rewritten here, since `groupCohomology.functor` and `groupCohomology` give the
  -- carrier of `H²(G, ℤ)` in two syntactically different forms.
  rfl

end TauCeti.TateCohomology
