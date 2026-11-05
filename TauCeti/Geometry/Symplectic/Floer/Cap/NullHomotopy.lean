/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Basic
public import TauCeti.Geometry.Symplectic.Floer.SphericalPeriodGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.NullHomotopy

/-!
# Cap classes of contractible loops in a space

Let `X` be a topological space with homomorphisms `ω : H₂(X; ℤ) →+ ℝ` and `c : H₂(X; ℤ) →+ ℤ`,
for a symplectic manifold the symplectic area and the first Chern class. A contractible
one-periodic orbit `γ` of a Hamiltonian is a contractible loop, which we base at `x = γ 0`. Its
raw caps are the homotopy classes of discs bounding it, modelled as the classes of
null-homotopies `Path.NullHomotopyClass γ`. These form a torsor under `π_2(X, x)`, which acts by
gluing spheres (`Path.NullHomotopyClass.instAddTorsor`). The area and Chern number of a sphere
are those of its Hurewicz class, so the abstract construction `TauCeti.Floer.CapClass` of
`TauCeti.Geometry.Symplectic.Floer.Cap.Basic` applies: the *cap classes*
`TauCeti.Floer.LoopCapClass ω c γ` of `γ` identify two raw caps when the sphere obtained by gluing
them along `γ` has zero area and zero Chern number. They form a torsor under the period group of
`π_2(X, x)`, which on a path-connected space is the spherical period group
`Γ = S ⧸ (ker ω ⊓ ker c)` (`TauCeti.Floer.SphericalPeriodGroup.homotopyGroupEquiv`).

A pair of pants with inputs `γ₁`, `γ₂` and output `γ₀` is a homotopy class `u` of homotopies from
the concatenation `γ₁.trans γ₂` to `γ₀`. Gluing caps of the inputs to `u`
(`Path.NullHomotopyClass.glue`) is equivariant under spheres in each input, so it descends to cap
classes as `TauCeti.Floer.LoopCapClass.glue ω c u`, which is equivariant under the period group in
each input. These are exactly the hypotheses of the recapping and cap-independence laws for the
product class `A = D₀ + u − D₁ − D₂` in `TauCeti.Geometry.Symplectic.Floer.Cap.Basic`, such as
`TauCeti.Floer.productClass_eq_add_sub` and
`TauCeti.Floer.add_sub_add_two_mul_chern_productClass_eq`. The product class of the classes of
actual caps `D₁`, `D₂`, `D₀` is the class of the sphere `D₀ -ᵥ glue u D₁ D₂`
(`TauCeti.Floer.LoopCapClass.productClass_glue_mk`).

## Main definitions

* `TauCeti.Floer.LoopCapClass ω c γ`: the cap classes of a contractible loop `γ`.
* `TauCeti.Floer.LoopCapClass.glue ω c u`: gluing cap classes of the inputs of a pair of pants `u`
  to a cap class of its output.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology and the pair-of-pants product.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology

namespace TauCeti.Floer

variable {X : Type} [TopologicalSpace X] {x : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

variable (ω c) in
/-- The **cap classes** of a contractible loop `γ` at `x`: classes of null-homotopies of `γ`,
two of which are identified when the sphere obtained by gluing them along `γ` has zero area and
zero first Chern number. It is a torsor under the period group of `π_2(X, x)`. -/
abbrev LoopCapClass (γ : Path x x) [Nonempty γ.NullHomotopyClass] : Type :=
  CapClass (ω.comp (hurewiczIntHom X x 1)) (c.comp (hurewiczIntHom X x 1)) γ.NullHomotopyClass

namespace LoopCapClass

variable {γ₁ γ₂ γ₀ : Path x x} [Nonempty γ₁.NullHomotopyClass] [Nonempty γ₂.NullHomotopyClass]
  [Nonempty γ₀.NullHomotopyClass]

variable (ω c) in
/-- **Gluing cap classes along a pair of pants.** A homotopy class `u` of homotopies from
`γ₁.trans γ₂` to `γ₀` glues cap classes of `γ₁` and `γ₂` to a cap class of `γ₀`, by gluing
representing caps (`Path.NullHomotopyClass.glue`). -/
def glue (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀) :
    LoopCapClass ω c γ₁ → LoopCapClass ω c γ₂ → LoopCapClass ω c γ₀ :=
  CapClass.map₂ (Path.NullHomotopyClass.glue u) (Path.NullHomotopyClass.glue_vadd_left u)
    (Path.NullHomotopyClass.glue_vadd_right u)

/-- The glued cap class of the classes of caps `D₁` and `D₂` is the class of the glued cap. -/
@[simp]
theorem glue_mk (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀) (D₁ : γ₁.NullHomotopyClass)
    (D₂ : γ₂.NullHomotopyClass) :
    glue ω c u (Quotient.mk'' D₁) (Quotient.mk'' D₂) =
      Quotient.mk'' (Path.NullHomotopyClass.glue u D₁ D₂) :=
  CapClass.map₂_mk _ _ _ D₁ D₂

/-- Recapping the first input of a pair of pants recaps the glued output by the same class. -/
theorem glue_vadd_left (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀)
    (g : PeriodGroup (ω.comp (hurewiczIntHom X x 1)) (c.comp (hurewiczIntHom X x 1)))
    (C₁ : LoopCapClass ω c γ₁) (C₂ : LoopCapClass ω c γ₂) :
    glue ω c u (g +ᵥ C₁) C₂ = g +ᵥ glue ω c u C₁ C₂ :=
  CapClass.map₂_vadd_left _ _ _ g C₁ C₂

/-- Recapping the second input of a pair of pants recaps the glued output by the same class. -/
theorem glue_vadd_right (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀)
    (g : PeriodGroup (ω.comp (hurewiczIntHom X x 1)) (c.comp (hurewiczIntHom X x 1)))
    (C₁ : LoopCapClass ω c γ₁) (C₂ : LoopCapClass ω c γ₂) :
    glue ω c u C₁ (g +ᵥ C₂) = g +ᵥ glue ω c u C₁ C₂ :=
  CapClass.map₂_vadd_right _ _ _ g C₁ C₂

/-- The class `A = D₀ + u − D₁ − D₂` of a pair of pants `u` relative to caps `D₁`, `D₂` of its
inputs and `D₀` of its output is the class of the sphere `D₀ -ᵥ glue u D₁ D₂` by which the output
cap differs from the glued cap. -/
@[simp]
theorem productClass_glue_mk (u : Path.Homotopic.Quotient (γ₁.trans γ₂) γ₀)
    (D₁ : γ₁.NullHomotopyClass) (D₂ : γ₂.NullHomotopyClass) (D₀ : γ₀.NullHomotopyClass) :
    productClass (glue ω c u) (Quotient.mk'' D₁ : LoopCapClass ω c γ₁)
        (Quotient.mk'' D₂ : LoopCapClass ω c γ₂) (Quotient.mk'' D₀ : LoopCapClass ω c γ₀) =
      ((D₀ -ᵥ Path.NullHomotopyClass.glue u D₁ D₂ : Additive (π_ 2 X x)) :
        PeriodGroup (ω.comp (hurewiczIntHom X x 1)) (c.comp (hurewiczIntHom X x 1))) :=
  productClass_map₂_mk _ _ _ D₁ D₂ D₀

end LoopCapClass

end TauCeti.Floer
