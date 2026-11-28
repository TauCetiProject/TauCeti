/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection

/-!
# Base change of a monoid scheme with the base as the first factor

The monoid structure on `S' ×_S G` over `S'` is transported from the monoidal pullback functor
through pullback symmetry. Its unit is the base change of the unit section of `G`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TauCeti.AlgebraicGeometry

namespace TauCeti.GroupScheme

universe u

noncomputable section

variable {S S' : Scheme.{u}} {G : Over S} [MonObj G] (g : S' ⟶ S)

/-- The monoid structure on `S' ×_S G` over `S'`, with the base change of the unit
section of `G` as its unit. -/
abbrev baseChangeMonObj : MonObj (Over.mk (pullback.fst g G.hom)) :=
  letI := Functor.monObjObj (F := Over.pullback g) G
  let e : (Over.pullback g).obj G ≅ Over.mk (pullback.fst g G.hom) :=
    Over.isoMk (pullbackSymmetry _ _) (by simp)
  let m := MonObj.ofIso e
  let one : 𝟙_ (Over S') ⟶ Over.mk (pullback.fst g G.hom) :=
    Over.homMk
      (baseChangeSection G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g))
      (baseChangeSection_fst ..)
  have h : m.one = one := by
    apply Over.OverMorphism.ext
    have hε : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.snd (𝟙 S) g =
        𝟙 S' := by simp
    have hε' : (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫ pullback.fst (𝟙 S) g = g := by
      calc
        _ = (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
            (pullback.fst (𝟙 S) g ≫ 𝟙 S) := by simp
        _ = g := by
          rw [pullback.condition, ← Category.assoc, hε]
          simp
    -- Compare the transported unit by its two pullback projections.
    change (Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G] ≫ e.hom).left = _
    apply pullback.hom_ext
    · simpa [e, one] using
        (baseChangeSection_fst G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)).symm
    · simpa [e, one, hε'] using
        (baseChangeSection_snd G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)).symm
  { m with
    one := one
    one_mul := by simpa only [h] using m.one_mul
    mul_one := by simpa only [h] using m.mul_one }

attribute [local instance] baseChangeMonObj

/-- The unit on `S' ×_S G` projects to the base morphism followed by the unit of `G`. -/
@[reassoc (attr := simp)]
theorem baseChangeMonObj_one_left_snd :
    η[Over.mk (pullback.fst g G.hom)].left ≫ pullback.snd g G.hom = g ≫ η[G].left :=
  baseChangeSection_snd G.hom η[G].left (η[G].w.trans Over.tensorUnit_hom) (Over.mk g)

/-- The multiplication on `S' ×_S G` projects to the multiplication on `G`
applied to the projections of both inputs. -/
@[reassoc (attr := simp)]
theorem baseChangeMonObj_mul_left_snd :
    μ[Over.mk (pullback.fst g G.hom)].left ≫ pullback.snd g G.hom =
      pullback.map _ _ _ _ (pullback.snd g G.hom) (pullback.snd g G.hom) g
        pullback.condition pullback.condition ≫ μ[G].left := by
  let e : (Over.pullback g).obj G ≅ Over.mk (pullback.fst g G.hom) :=
    Over.isoMk (pullbackSymmetry _ _) (by simp)
  -- Expose the multiplication field so the projection lemmas can see the product comparison.
  change ((e.inv ⊗ₘ e.inv) ≫ Functor.LaxMonoidal.μ (Over.pullback g) G G ≫
    (Over.pullback g).map μ[G] ≫ e.hom).left ≫ _ = _
  simp only [Over.comp_left, Category.assoc, e, Over.isoMk_hom_left,
    pullbackSymmetry_hom_comp_snd, Over.pullback_map_left, pullback.lift_fst]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.μ_pullback_left_fst_fst, Over.tensorHom_left,
      pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Over.mk_hom,
      Over.isoMk_inv_left, pullbackSymmetry_inv_comp_fst]
  · simp only [Category.assoc, Over.μ_pullback_left_fst_snd, Over.tensorHom_left,
      pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Over.mk_hom,
      Over.isoMk_inv_left, pullbackSymmetry_inv_comp_fst]

end

end TauCeti.GroupScheme
