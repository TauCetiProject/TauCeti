/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Topology.Homotopy.HomotopyGroup.Conjugation

/-!
# Transporting caps of loops along paths

The cap API of `TauCeti.Geometry.Symplectic.Floer.Cap.Loop` works with loops at one base
point `x`: a raw cap of a loop `γ` at `x` is a homotopy class of paths in the loop space `Ω X x`
from `γ` to the constant loop, and spheres at `x` act on raw caps by gluing at the centre. The
one-periodic orbits of a Hamiltonian have different base points, so comparing their caps, or
gluing them along a pair of pants whose seams run from the output orbit to the input orbits,
moves loops from one base point to another along a path `p` from `x` to `y`.

Conjugation by `p` moves a loop `γ` at `x` to the loop `p.conjLoop γ = p⁻¹ ⬝ (γ ⬝ p)` at `y`. It
moves a disc bounding `γ` to a disc bounding `p.conjLoop γ`: conjugate every loop of the disc,
then contract the conjugated constant loop along `Path.conjLoopContraction p`. This is
`TauCeti.Floer.RawCap.transport p`. A sphere glued to the disc moves by base-point change of
`π₂` along `p` (`TauCeti.Floer.RawCap.transport_vadd`), by
`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`. Base-point change does
not change the Hurewicz class of a sphere, so it does not change the class of the sphere in the
spherical period group `Γ` (`TauCeti.Floer.SphericalPeriodGroup.ofHomotopyGroup`). Hence
transport descends to cap classes, the raw caps modulo spheres of zero symplectic area and zero
first Chern number (`TauCeti.Floer.SphericalCapClass.transport`), where it is `Γ`-equivariant
(`TauCeti.Floer.SphericalCapClass.transport_vadd`) and, for a contractible loop on a
path-connected space, a bijection (`TauCeti.Floer.SphericalCapClass.transport_bijective`).

Transport is natural for gluing homotopies of loops
(`TauCeti.Floer.SphericalCapClass.transport_glue`). Together with the equivariance of gluing along
a pair of pants (`TauCeti.Floer.SphericalCapClass.pantsGlue_vadd_left`,
`TauCeti.Floer.SphericalCapClass.pantsGlue_vadd_right`), the equivariance of transport makes the
gluing `(q₁, q₂) ↦ pantsGlue P (transport p₁ q₁) (transport p₂ q₂)` of caps of orbits at the
endpoints of seams `p₁`, `p₂` equivariant in each input. So it is a cap-gluing map of the kind
taken by the product-class API of `TauCeti.Geometry.Symplectic.Floer.Cap.Basic`, such as
`TauCeti.Floer.productClass_eq_add_sub`.

## Main definitions

* `TauCeti.Floer.RawCap.transport p`: transport of raw caps along a path `p`.
* `TauCeti.Floer.SphericalCapClass.transport p`: transport of cap classes along `p`.

## Main results

* `TauCeti.Floer.RawCap.transport_vadd`, `TauCeti.Floer.RawCap.transport_vsub_transport`:
  transport moves glued spheres by base-point change of `π₂`.
* `TauCeti.Floer.SphericalCapClass.transport_vadd`,
  `TauCeti.Floer.SphericalCapClass.transport_vsub_transport`: transport of cap classes commutes
  with recapping and preserves the classes by which cap classes differ.
* `TauCeti.Floer.SphericalCapClass.transport_bijective`: for a contractible loop on a
  path-connected space, transport is a bijection of cap classes.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on capped loops.
* A. Hatcher, *Algebraic Topology*, Section 4.1, on the action of paths on `π₂`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace RawCap

variable {γ γ₁ γ₂ : Ω X x}

/-- **Transport of a raw cap along a path** `p` from `x` to `y`: conjugate every loop of the
disc by `p`, then contract the conjugated constant loop along `Path.conjLoopContraction p`. The
result is a raw cap of the conjugated loop `p.conjLoop γ`. -/
def transport (p : Path x y) (D : RawCap γ) : RawCap (p.conjLoop γ) :=
  (FundamentalGroupoid.map p.conjLoop).map D ≫ Path.Homotopic.Quotient.mk p.conjLoopContraction

theorem transport_def (p : Path x y) (D : RawCap γ) :
    transport p D =
      (FundamentalGroupoid.map p.conjLoop).map D ≫
        Path.Homotopic.Quotient.mk p.conjLoopContraction :=
  (rfl)

/-- Transport is natural for gluing a homotopy of loops to a cap. -/
@[simp]
theorem transport_comp (p : Path x y) (u : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (D : RawCap γ₂) :
    transport p (u ≫ D) = (FundamentalGroupoid.map p.conjLoop).map u ≫ transport p D := by
  rw [transport_def, transport_def, Functor.map_comp, Category.assoc]
  -- the objects `(FundamentalGroupoid.map p.conjLoop).obj ⟨γ⟩` and `⟨p.conjLoop γ⟩` agree by
  -- definition
  rfl

/-- **Transport moves a glued sphere by base-point change of `π₂`.** -/
@[simp]
theorem transport_vadd (p : Path x y) (a : Additive (π_ 2 X x)) (D : RawCap γ) :
    transport p (a +ᵥ D) = Additive.ofMul (homotopyGroupTransport p a.toMul) +ᵥ transport p D := by
  have h : p.loopSpaceTransport (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul) =
      fundamentalGroupLoopSpaceMulEquiv.symm (homotopyGroupTransport p a.toMul) := by
    rw [MulEquiv.eq_symm_apply, fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport,
      MulEquiv.apply_symm_apply]
  rw [vadd_def, vadd_def, toMul_ofMul, transport_def, transport_def, Functor.map_comp,
    Category.assoc, Path.map_comp_conjLoopContraction, h]
  exact (Category.assoc _ _ _).symm

/-- Transport moves the sphere by which two raw caps differ by base-point change of `π₂`. -/
@[simp]
theorem transport_vsub_transport (p : Path x y) (D' D : RawCap γ) :
    transport p D' -ᵥ transport p D =
      Additive.ofMul (homotopyGroupTransport p (D' -ᵥ D).toMul) := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  have : Nonempty (RawCap (p.conjLoop γ)) := ⟨transport p D⟩
  conv_lhs => rw [← vsub_vadd (G := Additive (π_ 2 X x)) D' D, transport_vadd]
  exact vadd_vsub _ _

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] {x y : X}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

variable {γ γ₁ γ₂ : Ω X x}

/-- **Transport of cap classes along a path** `p` from `x` to `y`, computed on representatives by
`TauCeti.Floer.RawCap.transport`. It is well defined because base-point change of `π₂` does not
change the class of a sphere in the period group. -/
def transport (p : Path x y) :
    SphericalCapClass ω c γ → SphericalCapClass ω c (p.conjLoop γ) :=
  Quotient.map' (RawCap.transport p) fun _ D' ⟨k, hk⟩ =>
    ⟨⟨Additive.ofMul (homotopyGroupTransport p (k : Additive (π_ 2 X x)).toMul), by
      rw [AddMonoidHom.mem_ker, SphericalPeriodGroup.ofHomotopyGroup_homotopyGroupTransport,
        ofMul_toMul]
      exact k.2⟩, by
      rw [← hk]
      exact (RawCap.transport_vadd p _ D').symm⟩

@[simp]
theorem transport_mk (p : Path x y) (D : RawCap γ) :
    transport p (mk ω c D) = mk ω c (RawCap.transport p D) := by
  rw [mk_def, mk_def, transport, Quotient.map'_mk'']

/-- Transport preserves the class of the period group by which two cap classes differ. -/
@[simp]
theorem transport_vsub_transport (p : Path x y) (q' q : SphericalCapClass ω c γ) :
    transport p q' -ᵥ transport p q = q' -ᵥ q := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D => rw [transport_mk, transport_mk, mk_vsub_mk, mk_vsub_mk, RawCap.transport_vsub_transport,
      SphericalPeriodGroup.ofHomotopyGroup_homotopyGroupTransport, ofMul_toMul]

/-- Transport is natural for gluing a homotopy of loops to a cap class. -/
@[simp]
theorem transport_glue (p : Path x y) (u : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (q : SphericalCapClass ω c γ₂) :
    transport p (glue u q) = glue (u.map p.conjLoop) (transport p q) := by
  induction q using induction_on with
  | h D =>
    rw [glue_mk, transport_mk, transport_mk, glue_mk, RawCap.transport_comp,
      FundamentalGroupoid.map_map]
    -- as in `RawCap.transport_comp`, the two sides differ only in how the objects are written
    rfl

variable [PathConnectedSpace X]

/-- **Transport of cap classes commutes with recapping.** -/
@[simp]
theorem transport_vadd (p : Path x y) (g : SphericalPeriodGroup ω c)
    (q : SphericalCapClass ω c γ) : transport p (g +ᵥ q) = g +ᵥ transport p q := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q using induction_on with
  | h D => rw [ofHomotopyGroup_vadd_mk, transport_mk, transport_mk, RawCap.transport_vadd,
      ← ofHomotopyGroup_vadd_mk, SphericalPeriodGroup.ofHomotopyGroup_homotopyGroupTransport,
      ofMul_toMul]

/-- **Transport of the cap classes of a contractible loop on a path-connected space is a
bijection.** -/
theorem transport_bijective [Nonempty (RawCap γ)] (p : Path x y) :
    Function.Bijective (transport (ω := ω) (c := c) (γ := γ) p) := by
  have : Nonempty (RawCap (p.conjLoop γ)) := ⟨RawCap.transport p (Classical.arbitrary _)⟩
  refine ⟨fun q q' h => ?_, fun q' => ?_⟩
  · rw [← vsub_eq_zero_iff_eq, ← transport_vsub_transport p, h, vsub_self]
  · obtain ⟨q₀⟩ : Nonempty (SphericalCapClass ω c γ) := inferInstance
    exact ⟨(q' -ᵥ transport p q₀) +ᵥ q₀, by rw [transport_vadd, vsub_vadd]⟩

end SphericalCapClass

end Spherical

end TauCeti.Floer
