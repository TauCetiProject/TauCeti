/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.DenseTorus
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
# The dense torus of a toric fan

The zero cone is a cone of every nonempty finite fan.  This module places the generic dense-torus
scheme from `Algebraic.DenseTorus` in the toric scheme of a finite fan and records the canonical
open immersion into the realization.  The compatibility theorem says that this inclusion is
obtained on every affine chart by the face localization from the zero cone.

## Main declarations

* `TauCeti.Toric.Fan.denseTorus`: the zero-cone dense torus attached to a fan.
* `TauCeti.Toric.Fan.denseTorusι`: the canonical inclusion into a nonempty fan realization.
* `TauCeti.Toric.Fan.denseTorusι_eq`: independence of the nonemptiness witness.
* `TauCeti.Toric.Fan.isOpenImmersion_denseTorusι`: the inclusion is an open immersion.
* `TauCeti.Toric.Fan.denseTorusι_face`: the inclusion agrees with face localization on every
  affine chart.
* `TauCeti.Toric.Fan.denseTorusι_eq_affineToricChartι`: the inclusion is the chart inclusion of
  the zero cone.
* `TauCeti.Toric.Fan.isIso_denseTorusι_ofCone_bot`: the toric scheme of the fan of the zero cone
  is its dense torus.
* `TauCeti.Toric.Fan.mem_dualSemigroup_ofCone_bot`: every integral character is nonnegative on the
  cones of the fan of the zero cone.
* `TauCeti.Toric.FanHom.denseTorusι_comp_algebraicMap`: a toric map restricts on dense tori to
  the torus morphism induced by its lattice map.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3--1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.3 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The dense torus of a fan is the zero-cone dense torus of its integral lattice. -/
noncomputable abbrev denseTorus (Φ : Fan i) : Scheme :=
  denseTorusScheme Φ.lattice

/-- The zero cone selected from a nonempty fan.  This is an implementation helper for the
canonical inclusion; the public inclusion below takes the nonemptiness proof directly. -/
private noncomputable def botCone (Φ : Fan i) (hΦ₀ : Nonempty Φ.cones) : Φ.cones :=
  ⟨⊥, Φ.bot_mem hΦ₀.some.property⟩

/-- The canonical inclusion of the dense torus for a nonempty finite toric fan. -/
noncomputable def denseTorusι (Φ : Fan i)
    (hΦ₀ : Nonempty Φ.cones) : Φ.denseTorus ⟶ Φ.algebraicRealization :=
  Φ.affineToricChartι (botCone Φ hΦ₀)

/-- The dense torus is an open subscheme of every nonempty finite toric fan realization. -/
instance isOpenImmersion_denseTorusι (Φ : Fan i)
    (hΦ₀ : Nonempty Φ.cones) : IsOpenImmersion (Φ.denseTorusι hΦ₀) :=
  Φ.isOpenImmersion_affineToricChartι (botCone Φ hΦ₀)

/-- The dense-torus inclusion is independent of the proof witnessing fan nonemptiness. -/
theorem denseTorusι_eq (Φ : Fan i) (hΦ₀ hΦ₁ : Nonempty Φ.cones) :
    Φ.denseTorusι hΦ₀ = Φ.denseTorusι hΦ₁ := by
  let σ : Φ.cones := botCone Φ hΦ₀
  have hσ : (Nonempty.intro σ) = hΦ₀ := by rfl
  rw [← hσ]

/-- On every affine chart, the dense-torus inclusion is the face localization from the zero cone. -/
theorem denseTorusι_face (Φ : Fan i) (σ : Φ.cones) :
    Φ.denseTorusι (Nonempty.intro σ) =
      faceAffineToricSchemeMap Φ.lattice
          ((Φ.isToricCone σ.2).salient.bot_isFaceOf) ≫
        Φ.affineToricChartι σ := by
  have hbot : (⊥ : PointedCone ℝ V).IsFaceOf σ.1 :=
    (Φ.isToricCone σ.2).salient.bot_isFaceOf
  symm
  simpa [denseTorusι, denseTorus, denseTorusScheme, botCone] using
    (faceAffineToricSchemeMap_comp_affineToricChartι (Φ := Φ)
      (τ := botCone Φ (Nonempty.intro σ)) (σ := σ) hbot)

/-- The dense-torus inclusion is the affine chart inclusion of the zero cone. -/
theorem denseTorusι_eq_affineToricChartι (Φ : Fan i) (hΦ₀ : Nonempty Φ.cones)
    (h : (⊥ : PointedCone ℝ V) ∈ Φ.cones) :
    Φ.denseTorusι hΦ₀ = Φ.affineToricChartι ⟨⊥, h⟩ := by
  rw [Φ.denseTorusι_eq hΦ₀ (Nonempty.intro ⟨⊥, h⟩), denseTorusι_face Φ ⟨⊥, h⟩,
    faceAffineToricSchemeMap_id, Category.id_comp]

/-- The toric scheme of the fan of the zero cone is the dense torus: its dense-torus inclusion is
an isomorphism. -/
instance isIso_denseTorusι_ofCone_bot (hi : IsIntegralLattice i)
    (h : Nonempty (ofCone hi (isToricCone_bot i)).cones) :
    IsIso ((ofCone hi (isToricCone_bot i)).denseTorusι h) := by
  rw [denseTorusι_eq_affineToricChartι _ h ((mem_ofCone_cones hi _).2 (.refl ⊥))]
  infer_instance

/-- Every integral character is nonnegative on every cone of the fan of the zero cone, since that
fan has the zero cone as its only cone. -/
theorem mem_dualSemigroup_ofCone_bot (hi : IsIntegralLattice i) (m : N →+ ℤ)
    (σ : (ofCone hi (isToricCone_bot i)).cones) :
    m ∈ dualSemigroup (ofCone hi (isToricCone_bot i)).lattice σ.1 := by
  rw [le_bot_iff.mp ((mem_ofCone_cones hi (isToricCone_bot i)).mp σ.2).le]
  simp

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanHom

universe u

variable {N N' : Type u} {V V' : Type*} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- On dense tori, the toric map of a fan morphism is the torus morphism induced by its lattice
map. -/
@[reassoc]
theorem denseTorusι_comp_algebraicMap (f : FanHom Φ Ψ) (hΦ₀ : Nonempty Φ.cones) :
    Φ.denseTorusι hΦ₀ ≫ f.algebraicMap =
      affineToricSchemeMap (σ := ⊥) (τ := ⊥) Φ.lattice Ψ.lattice f.latticeMap f.realMap
          f.map_lattice (by simp [Set.MapsTo]) ≫
        Ψ.denseTorusι ⟨⟨_, f.leastCone_mem hΦ₀.some.2⟩⟩ := by
  have hΦ : (⊥ : PointedCone ℝ V) ∈ Φ.cones := Φ.bot_mem hΦ₀.some.2
  have hΨ : (⊥ : PointedCone ℝ V') ∈ Ψ.cones := Ψ.bot_mem (f.leastCone_mem hΦ₀.some.2)
  rw [Φ.denseTorusι_eq_affineToricChartι hΦ₀ hΦ, Ψ.denseTorusι_eq_affineToricChartι _ hΨ]
  exact f.affineToricChartι_comp_algebraicMap_of_leastCone_eq ⟨⊥, hΦ⟩ ⟨⊥, hΨ⟩
    (le_antisymm (f.leastCone_le hΦ hΨ (Submodule.map_bot _).le) bot_le) (by simp [Set.MapsTo])

end TauCeti.Toric.FanHom
