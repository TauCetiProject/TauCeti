/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic

/-!
# Products of scheme compactifications over the base

Compactifications `X ⟶ Xbar ⟶ S` of `f` and `Y ⟶ Ybar ⟶ S` of `g` give a compactification
of the fibre product `X ×_S Y ⟶ S`: the ambient scheme is `Xbar ×_S Ybar`, the interior map
is the product `pullback.map` of the two open immersions, and the proper map is the projection
to `Xbar` followed by its proper structure map. Quasi-compact open immersions and proper
morphisms are stable under base change and composition, which is all the construction uses.

Maps of compactifications multiply functorially, so the product is a functor on the product
category; products of closed immersions of compactifications are closed immersions. The product
of the identity compactifications of two proper morphisms is the identity compactification of
their fibre product.

Scheme-theoretic density of the interior is not preserved by products in general, but it is
when `f` and the structure map of the second compactification are flat
(`Compactification.prod_isSchemeTheoreticallyDominant`). The interior map factors as the base
change of one dense open immersion along a flat map followed by the base change of the other,
and Mathlib's `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` applies to each.
Over the spectrum of a field every morphism is flat and instance search supplies both
hypotheses, so products of dense compactifications are dense there. In general one takes the
dense replacement of the product.

## Main declarations

* `TauCeti.Compactification.prod`: the product of two compactifications over the base.
* `TauCeti.Compactification.prodMap`: the product of two maps of compactifications.
* `TauCeti.Compactification.prodFunctor`: the product as a functor of two variables.
* `TauCeti.Compactification.prod_isSchemeTheoreticallyDominant`: density of the product
  under flatness.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RB).
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

namespace Compactification

noncomputable section

/-- The product over `S` of compactifications of `f` and `g`, a compactification of the fibre
product `pullback.fst f g ≫ f : X ×_S Y ⟶ S`. Its ambient scheme is `pullback C.p D.p`, its
interior map is `pullback.map` of the two interior maps, and its proper map is
`pullback.fst C.p D.p ≫ C.p`. -/
-- Exposure and implicit reducibility keep dependent projection formulas usable across modules.
@[expose, implicit_reducible] def prod (C : Compactification f) (D : Compactification g) :
    Compactification (pullback.fst f g ≫ f) :=
  @ofHom _ _ _ _ (pullback.map f g C.p D.p C.j D.j (𝟙 S) (by simp) (by simp))
    (pullback.fst C.p D.p ≫ C.p)
    (MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstanceAs (IsOpenImmersion C.j))
      (inferInstanceAs (IsOpenImmersion D.j)) C.obj.ι_π.symm D.obj.ι_π.symm)
    (MorphismProperty.pullbackMap (P := @QuasiCompact) (inferInstanceAs (QuasiCompact C.j))
      (inferInstanceAs (QuasiCompact D.j)) C.obj.ι_π.symm D.obj.ι_π.symm)
    inferInstance (by simp)

@[simp]
theorem prod_Xbar (C : Compactification f) (D : Compactification g) :
    (C.prod D).Xbar = pullback C.p D.p :=
  (rfl)

@[simp]
theorem prod_j (C : Compactification f) (D : Compactification g) :
    (C.prod D).j = pullback.map f g C.p D.p C.j D.j (𝟙 S) (by simp) (by simp) :=
  (rfl)

@[simp]
theorem prod_p (C : Compactification f) (D : Compactification g) :
    (C.prod D).p = pullback.fst C.p D.p ≫ C.p :=
  (rfl)

/-- The product of two maps of compactifications, on the fibre products of their ambient
schemes. -/
def prodMap {C C' : Compactification f} {D D' : Compactification g} (h : C ⟶ C') (k : D ⟶ D') :
    C.prod D ⟶ C'.prod D' :=
  ObjectProperty.homMk
    { h := pullback.map C.p D.p C'.p D'.p h.hom.h k.hom.h (𝟙 S) (by simp) (by simp)
      ι_h := by
        dsimp only [prod, ofHom]
        rw [pullback.map_comp]
        simp
      h_π := by simp }

@[simp]
theorem prodMap_hom_h {C C' : Compactification f} {D D' : Compactification g}
    (h : C ⟶ C') (k : D ⟶ D') :
    (prodMap h k).hom.h =
      pullback.map C.p D.p C'.p D'.p h.hom.h k.hom.h (𝟙 S) (by simp) (by simp) :=
  (rfl)

/-- Products of closed immersions of compactifications are closed immersions. -/
instance {C C' : Compactification f} {D D' : Compactification g} (h : C ⟶ C') (k : D ⟶ D')
    [IsClosedImmersion h.hom.h] [IsClosedImmersion k.hom.h] :
    IsClosedImmersion (prodMap h k).hom.h := by
  -- Instance search does not reach composition stability through `IsMultiplicative` here.
  have : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstanceAs (IsClosedImmersion h.hom.h)) (inferInstanceAs (IsClosedImmersion k.hom.h))
    h.hom.h_π.symm k.hom.h_π.symm

variable (f g) in
/-- The product of compactifications as a functor on the product category. -/
-- The object equations must remain available when elaborating dependent morphism formulas.
@[expose, implicit_reducible, simps obj map]
def prodFunctor :
    Compactification f × Compactification g ⥤ Compactification (pullback.fst f g ≫ f) where
  obj C := C.1.prod C.2
  map h := prodMap h.1 h.2
  map_id C := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    -- Normalize the identity map's dependent endpoint before categorical simplification.
    dsimp only [prod, ofHom]
    apply pullback.hom_ext <;> simp
  map_comp h k := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    apply pullback.hom_ext <;> simp

/-- The product of the identity compactifications of two proper morphisms is the identity
compactification of their fibre product. -/
theorem identity_prod_identity [IsProper f] [IsProper g] :
    (identity f).prod (identity g) = identity (pullback.fst f g ≫ f) := by
  -- Both sides are built by `ofHom` on the same ambient scheme and proper map.
  dsimp only [prod, identity, ofHom]
  congr
  exact pullback.map_id

/-- The product of compactifications with scheme-theoretically dense interiors has dense
interior when `f` and the structure map of the second compactification are flat. -/
instance prod_isSchemeTheoreticallyDominant (C : Compactification f) (D : Compactification g)
    [IsSchemeTheoreticallyDominant C.j] [IsSchemeTheoreticallyDominant D.j] [Flat f]
    [Flat D.p] : IsSchemeTheoreticallyDominant (C.prod D).j := by
  -- Enlarge the second factor first, then the first factor.
  let a : pullback f g ⟶ pullback f D.p :=
    pullback.map f g f D.p (𝟙 X) D.j (𝟙 S) (by simp) (by simp)
  let b : pullback f D.p ⟶ pullback C.p D.p :=
    pullback.map f D.p C.p D.p C.j (𝟙 _) (𝟙 S) (by simp) (by simp)
  -- `a` is the base change of `D.j` along the flat projection `pullback.snd f D.p`.
  have ha : IsPullback (pullback.snd f g) a D.j (pullback.snd f D.p) :=
    IsPullback.of_bot (by simpa [a] using (IsPullback.of_hasPullback f g).flip) (by simp [a])
      (IsPullback.of_hasPullback f D.p).flip
  -- `b` is the base change of `C.j` along the flat projection `pullback.fst C.p D.p`.
  have hb : IsPullback (pullback.fst f D.p) b C.j (pullback.fst C.p D.p) :=
    IsPullback.of_bot (by simpa [b] using IsPullback.of_hasPullback f D.p) (by simp [b])
      (IsPullback.of_hasPullback C.p D.p)
  have := IsSchemeTheoreticallyDominant.of_isPullback ha
  have := IsSchemeTheoreticallyDominant.of_isPullback hb
  have hab : (C.prod D).j = a ≫ b := by
    simp only [prod_j, a, b, pullback.map_comp]
    simp
  rw [hab]
  infer_instance

end

end Compactification

end TauCeti
