/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Loop
public import TauCeti.Topology.Homotopy.HomotopyGroup.Conjugation

/-!
# Transporting caps of loops along paths and along free homotopies of loops

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

A Floer cylinder, or an end of a pair of pants, is a homotopy of loops whose base point moves: a
`ContinuousMap.HomotopyWith` `F` of maps `I → X` through loops, from a loop `γ₀` at `x` to a loop
`γ₁` at `y`, whose seam `F.basepointPath` runs from `x` to `y`. Caps of `γ₀` lift along `F` to caps
of `γ₁`: transport a cap along the seam, which gives a cap of `F.basepointPath.conjLoop γ₀`, then
glue the based homotopy of loops `F.conjLoopHom` from this loop to `γ₁`. This is
`TauCeti.Floer.RawCap.transportAlong F` on raw caps and
`TauCeti.Floer.SphericalCapClass.transportAlong F` on cap classes. On cap classes it commutes with
recapping (`TauCeti.Floer.SphericalCapClass.transportAlong_vadd`) and, on a path-connected space,
it is a bijection (`TauCeti.Floer.SphericalCapClass.transportAlong_bijective`): the cap classes
lift uniquely along paths of loops. When the seam stays at `x`, transport along `F` is gluing the
homotopy of loops `F.loopPath` backwards
(`TauCeti.Floer.SphericalCapClass.transportAlong_of_forall_eq`), so the constant homotopy
transports every cap class to itself (`TauCeti.Floer.SphericalCapClass.transportAlong_refl`).
Measured against a cap class `q₁` of the output, a cylinder `F` with input cap class `q₀` has the
class `q₁ -ᵥ transportAlong F q₀` in `Γ`.

## Main definitions

* `TauCeti.Floer.RawCap.transport p`: transport of raw caps along a path `p`.
* `TauCeti.Floer.SphericalCapClass.transport p`: transport of cap classes along `p`.
* `TauCeti.Floer.RawCap.transportAlong F`, `TauCeti.Floer.SphericalCapClass.transportAlong F`:
  transport of raw caps and of cap classes along a free homotopy of loops `F`.

## Main results

* `TauCeti.Floer.RawCap.transport_vadd`, `TauCeti.Floer.RawCap.transport_vsub_transport`:
  transport moves glued spheres by base-point change of `π₂`.
* `TauCeti.Floer.SphericalCapClass.transport_vadd`,
  `TauCeti.Floer.SphericalCapClass.transport_vsub_transport`: transport of cap classes commutes
  with recapping and preserves the classes by which cap classes differ.
* `TauCeti.Floer.SphericalCapClass.transport_bijective`: for a contractible loop on a
  path-connected space, transport is a bijection of cap classes.
* `TauCeti.Floer.RawCap.transport_refl`: transport along a constant path only reparametrizes.
* `TauCeti.Floer.SphericalCapClass.transportAlong_vadd`,
  `TauCeti.Floer.SphericalCapClass.transportAlong_vsub_transportAlong`,
  `TauCeti.Floer.SphericalCapClass.transportAlong_bijective`: transport along a free homotopy of
  loops commutes with recapping and is a bijection of cap classes.
* `TauCeti.Floer.SphericalCapClass.transportAlong_of_forall_eq`: along a homotopy of loops with
  a fixed base point, transport is gluing.

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


/-- **Transport along the constant path** is gluing the reparametrization
`Path.conjLoopReflPath γ` backwards: conjugating by a constant path only reparametrizes every loop
of the disc. -/
theorem transport_refl (D : RawCap γ) :
    transport (Path.refl x) D =
      inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.conjLoopReflPath γ))) ≫
        D := by
  rw [IsIso.eq_inv_comp, transport_def]
  -- the objects of `Path.mk_conjLoopReflPath_comp_map D` are those of the goal only up to
  -- unfolding the functor `FundamentalGroupoid.map`, so the steps are chained as terms
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) (Path.mk_conjLoopReflPath_comp_map D)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (D ≫ ·) (Path.mk_conjLoopReflPath_comp_mk_conjLoopContraction x)).trans
          (Category.comp_id D)

/-- Transport along equal paths agrees up to the identification of the conjugated loops. -/
private theorem transport_eq_eqToHom_comp {p q : Path x y} (h : p = q) (D : RawCap γ) :
    transport p D =
      eqToHom (congrArg (fun r : Path x y => (⟨r.conjLoop γ⟩ : FundamentalGroupoid (Ω X y))) h) ≫
        transport q D := by
  subst h
  exact (Category.id_comp _).symm

end RawCap

end Raw

section FreeHomotopy

open ContinuousMap unitInterval

variable {X : Type*} [TopologicalSpace X] {x y : X} {γ₀ : Ω X x} {γ₁ : Ω X y}

namespace RawCap

/-- **Transport of a raw cap along a free homotopy of loops** `F` from `γ₀` to `γ₁`, a cylinder
whose seam `F.basepointPath` runs from the base point of `γ₀` to that of `γ₁`: transport the disc
along the seam, which gives a disc bounding `F.basepointPath.conjLoop γ₀`, then glue the based
homotopy of loops `F.conjLoopHom` from this loop to `γ₁`. This is the lift of `F` to the caps:
following a cap of `γ₀` along the loops of `F` gives a cap of `γ₁`. -/
def transportAlong (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) (D : RawCap γ₀) :
    RawCap γ₁ :=
  inv F.conjLoopHom ≫ transport F.basepointPath D

theorem transportAlong_def (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)
    (D : RawCap γ₀) : transportAlong F D = inv F.conjLoopHom ≫ transport F.basepointPath D :=
  (rfl)

/-- **Transport along a free homotopy moves a glued sphere** by base-point change of `π₂` along the
seam of the homotopy. -/
@[simp]
theorem transportAlong_vadd (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)
    (a : Additive (π_ 2 X x)) (D : RawCap γ₀) :
    transportAlong F (a +ᵥ D) =
      Additive.ofMul (homotopyGroupTransport F.basepointPath a.toMul) +ᵥ transportAlong F D := by
  rw [transportAlong_def, transportAlong_def, transport_vadd, comp_vadd]

/-- Transport along a free homotopy moves the sphere by which two raw caps differ by base-point
change of `π₂` along the seam of the homotopy. -/
@[simp]
theorem transportAlong_vsub_transportAlong
    (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) (D' D : RawCap γ₀) :
    transportAlong F D' -ᵥ transportAlong F D =
      Additive.ofMul (homotopyGroupTransport F.basepointPath (D' -ᵥ D).toMul) := by
  rw [transportAlong_def, transportAlong_def, comp_vsub_comp, transport_vsub_transport]

/-- **Transport along a homotopy of loops with a fixed base point** is gluing the homotopy of
loops `F.loopPath h` backwards, the gluing of `TauCeti.Floer.RawCap`. -/
theorem transportAlong_of_forall_eq {γ₀ γ₁ : Ω X x}
    (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) (h : ∀ s, F (s, 0) = x)
    (D : RawCap γ₀) :
    transportAlong F D =
      inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F.loopPath h))) ≫ D := by
  rw [transportAlong_def, F.conjLoopHom_eq_eqToHom_comp h,
    transport_eq_eqToHom_comp (F.basepointPath_eq_refl h), transport_refl]
  simp

end RawCap

end FreeHomotopy

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


section FreeHomotopy

open ContinuousMap unitInterval

variable {X : Type} [TopologicalSpace X] {x y : X} {γ₀ : Ω X x} {γ₁ : Ω X y}
  {ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ}
  {c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ}

namespace SphericalCapClass

/-- **Transport of cap classes along a free homotopy of loops** `F` from `γ₀` to `γ₁`: transport
along the seam `F.basepointPath`, then glue the based homotopy of loops `F.conjLoopHom`. It is
computed on representatives by `TauCeti.Floer.RawCap.transportAlong`
(`TauCeti.Floer.SphericalCapClass.transportAlong_mk`). -/
def transportAlong (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) :
    SphericalCapClass ω c γ₀ → SphericalCapClass ω c γ₁ :=
  glue (inv F.conjLoopHom) ∘ transport F.basepointPath

@[simp]
theorem transportAlong_mk (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)
    (D : RawCap γ₀) : transportAlong F (mk ω c D) = mk ω c (RawCap.transportAlong F D) := by
  rw [transportAlong, Function.comp_apply, transport_mk, glue_mk, RawCap.transportAlong_def]

/-- Transport along a free homotopy preserves the class of the period group by which two cap
classes differ. -/
@[simp]
theorem transportAlong_vsub_transportAlong
    (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) (q' q : SphericalCapClass ω c γ₀) :
    transportAlong F q' -ᵥ transportAlong F q = q' -ᵥ q := by
  rw [transportAlong, Function.comp_apply, Function.comp_apply, glue_vsub_glue,
    transport_vsub_transport]

/-- **Transport along a homotopy of loops with a fixed base point** is gluing the homotopy of
loops `F.loopPath h` backwards. -/
theorem transportAlong_of_forall_eq {γ₀ γ₁ : Ω X x}
    (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) (h : ∀ s, F (s, 0) = x)
    (q : SphericalCapClass ω c γ₀) :
    transportAlong F q =
      glue (inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F.loopPath h)))) q := by
  induction q using induction_on with
  | h D => rw [transportAlong_mk, glue_mk, RawCap.transportAlong_of_forall_eq F h]

/-- **Transport along the constant homotopy of a loop** is the identity. -/
@[simp]
theorem transportAlong_refl {γ : Ω X x} (q : SphericalCapClass ω c γ) :
    transportAlong (HomotopyWith.refl (P := fun g : C(I, X) => g 0 = g 1) (γ : C(I, X))
      (γ.source.trans γ.target.symm)) q = q := by
  have h : ∀ s, HomotopyWith.refl (P := fun g : C(I, X) => g 0 = g 1) (γ : C(I, X))
      (γ.source.trans γ.target.symm) (s, 0) = x := fun _ => γ.source
  have hP : (HomotopyWith.refl (P := fun g : C(I, X) => g 0 = g 1) (γ : C(I, X))
      (γ.source.trans γ.target.symm)).loopPath h = Path.refl γ :=
    Path.ext (funext fun _ => Path.ext (funext fun t => by simp))
  rw [transportAlong_of_forall_eq _ h, hP, Path.Homotopic.Quotient.mk_refl]
  exact (congrArg (glue · q) (IsIso.inv_id (X := (⟨γ⟩ : FundamentalGroupoid (Ω X x))))).trans
    (glue_id q)

variable [PathConnectedSpace X]

/-- **Transport along a free homotopy commutes with recapping.** -/
@[simp]
theorem transportAlong_vadd (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)
    (g : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ₀) :
    transportAlong F (g +ᵥ q) = g +ᵥ transportAlong F q := by
  rw [transportAlong, Function.comp_apply, Function.comp_apply, transport_vadd, glue_vadd]

/-- **Transport of cap classes along a free homotopy of loops is a bijection**: this is path
lifting of the cap classes along paths of loops. When `γ₀` is not contractible, neither is `γ₁`,
and both sets of cap classes are empty. -/
theorem transportAlong_bijective (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1) :
    Function.Bijective (transportAlong (ω := ω) (c := c) F) := by
  by_cases h : Nonempty (RawCap γ₀)
  · exact (glueEquiv (inv F.conjLoopHom)).bijective.comp (transport_bijective F.basepointPath)
  have : IsEmpty (RawCap γ₀) := not_nonempty_iff.1 h
  -- a cap of `γ₁` glued to `F.conjLoopHom` caps `F.basepointPath.conjLoop γ₀`, so `γ₀` would be
  -- null-homotopic
  have : IsEmpty (RawCap γ₁) := ⟨fun D => h <| RawCap.nonempty_iff.2 <|
    Path.Homotopic.of_conj_nullhomotopic (α := F.basepointPath.symm) <| by
      have hD := RawCap.nonempty_iff.1 ⟨F.conjLoopHom ≫ D⟩
      rw [Path.conjLoop_apply] at hD
      rw [Path.symm_symm]
      exact (Path.Homotopic.trans_assoc _ _ _).trans hD⟩
  exact ⟨fun q => isEmptyElim (induction_on (motive := fun _ => False) q isEmptyElim),
    fun q => isEmptyElim (induction_on (motive := fun _ => False) q isEmptyElim)⟩

end SphericalCapClass

end FreeHomotopy

end TauCeti.Floer
