/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.TorusClass
public import TauCeti.Topology.MappingTorus.Section

/-!
# Torus classes of loops of seamed paths

Let `φ : F ≃ₜ F` be a homeomorphism with mapping torus `Y_φ`. A `φ`-seamed path `γ`, a path with
`γ 1 = φ (γ 0)`, is a section of the projection `Y_φ → S¹`
(`TauCeti.SeamedPath.sectionHomeomorph`), and so a free loop of `Y_φ`
(`TauCeti.SeamedPath.sectionLoop`). A loop `t ↦ γ_t` of seamed paths therefore sweeps out the torus
`(s, t) ↦ mk φ (γ_t s) s` in the mapping torus. This is a torus in `Y_φ`, not in general the image
of a torus or of a sphere in `F`.

The **torus class** of a loop of seamed paths (`TauCeti.SeamedPath.torusClassHom`) is the class of
this torus in `H₂(Y_φ; ℤ)`: the torus class `TauCeti.freeLoopTorusClassHom` of the loop of free
loops `t ↦ sectionLoop φ γ_t`. It is a homomorphism on the fundamental group of the space of
seamed paths. In the Floer theory of a symplectomorphism `φ`, whose configuration space is the
space of `φ`-seamed paths, the symplectic area and the first Chern number are evaluated on these
classes; they play the role that the classes of spheres play for the contractible free loops of
Hamiltonian Floer theory.

## Main definitions

* `TauCeti.SeamedPath.torusClassHom φ γ`: the torus class `π₁(SeamedPath φ, γ) → H₂(Y_φ; ℤ)` of
  loops of `φ`-seamed paths.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* S. Dostoglou and D. A. Salamon, *Self-dual instantons and holomorphic curves*, Ann. of Math. 139
  (1994), 581–640.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

namespace TauCeti.SeamedPath

variable {F : Type} [TopologicalSpace F] (φ : F ≃ₜ F)

/-- **The torus class of a loop of seamed paths**: the homomorphism
`π₁(SeamedPath φ, γ) → H₂(Y_φ; ℤ)` sending a loop `t ↦ γ_t` of `φ`-seamed paths at `γ` to the class
of the torus `(s, t) ↦ mk φ (γ_t s) s` that it sweeps out in the mapping torus. It is the torus
class `TauCeti.freeLoopTorusClassHom` of the loop of free loops `t ↦ sectionLoop φ γ_t`. -/
def torusClassHom (γ : SeamedPath φ) :
    Additive (HomotopyGroup (Fin 1) (SeamedPath φ) γ) →+
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
        (TopCat.of (MappingTorus φ)) :=
  (freeLoopTorusClassHom (MappingTorus φ) (sectionLoop φ γ)).comp
    (HomotopyGroup.mapHom (sectionLoop φ) rfl).toAdditive

/-- The torus class of a loop of seamed paths is the torus class of its loop of free loops of the
mapping torus. -/
theorem torusClassHom_apply (γ : SeamedPath φ)
    (a : Additive (HomotopyGroup (Fin 1) (SeamedPath φ) γ)) :
    torusClassHom φ γ a =
      freeLoopTorusClassHom (MappingTorus φ) (sectionLoop φ γ)
        (Additive.ofMul (HomotopyGroup.map (sectionLoop φ) rfl a.toMul)) :=
  (rfl)

end TauCeti.SeamedPath
