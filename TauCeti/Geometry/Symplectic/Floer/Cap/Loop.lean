/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Torsor.Quotient
public import TauCeti.CategoryTheory.Groupoid.Torsor
public import TauCeti.Geometry.Symplectic.Floer.Cap.Basic
public import TauCeti.Geometry.Symplectic.Floer.SphericalPeriodGroup
public import TauCeti.GroupTheory.QuotientGroup.KerEquiv
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
public import TauCeti.Topology.PathSpace.Prepend

/-!
# Caps of contractible loops

Let `γ` be a loop in a space `X` based at `x`. A *raw cap* of `γ` (`TauCeti.Floer.RawCap γ`) is a
homotopy class, relative to its endpoints, of paths `s ↦ D_s` in the loop space `Ω X x` from
`D_0 = γ` to the constant loop `D_1`. Such a path is the map `(s, t) ↦ D_s t` of the square whose
bottom edge is `γ` and whose three other edges go to `x`; that is, a disc bounding `γ`. A homotopy
of such paths is a homotopy of discs relative to the boundary. The raw caps are the
morphisms from `γ` to the constant loop in the fundamental groupoid of `Ω X x`, so:

* `γ` has a raw cap exactly when it is null-homotopic (`TauCeti.Floer.RawCap.nonempty_iff`).
* Gluing a sphere at the centre of a disc is postcomposition with a loop of loops at the
  constant loop. By `HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv`, these loops of loops
  form `π₂(X, x)`. Two raw caps differ by a unique sphere, so the raw caps of a contractible
  loop form a torsor under `π₂(X, x)`
  (`TauCeti.Floer.RawCap.instAddTorsor`, from `CategoryTheory.End.torsorRight`). Here
  `D' -ᵥ D` is the sphere obtained by running `D` backwards from the centre to `γ` and then
  `D'` from `γ` back to the centre.
* A homotopy of loops `p` from `γ₁` to `γ₂`, which is a cylinder whose seam stays at `x`, glues
  to a cap `D` of `γ₂` and gives the cap `p ≫ D` of `γ₁`. This commutes with gluing spheres and
  preserves differences of caps (`TauCeti.Floer.RawCap.comp_vadd`,
  `TauCeti.Floer.RawCap.comp_vsub_comp`).
* A homotopy of loops `u` from `γ₀` to `γ₁.trans γ₂`, a pair of pants with inputs `γ₁`, `γ₂` and
  output `γ₀`, glues caps `D₁` of `γ₁` and `D₂` of `γ₂` to the cap
  `TauCeti.Floer.RawCap.glue₂ u D₁ D₂` of `γ₀`: follow `u`, then concatenate `D₁` and `D₂`
  pointwise in the loop space. Gluing a sphere to either input glues it to the output
  (`TauCeti.Floer.RawCap.glue₂_vadd_left`, `TauCeti.Floer.RawCap.glue₂_vadd_right`), because
  concatenating every loop of a loop of loops with the constant loop does not change its class
  (`Path.Homotopic.Quotient.cast_map_trans_prod_refl`).

Capped Hamiltonian Floer theory works with caps modulo spheres of zero symplectic area and zero
first Chern number. For homomorphisms `ω` and `c` on `H₂(X; ℤ)`, the *cap classes* of `γ`
(`TauCeti.Floer.SphericalCapClass ω c γ`) are the raw caps modulo spheres whose Hurewicz classes
lie in the joint kernel of `ω` and `c`. On a path-connected space every class of the period
group `Γ = TauCeti.Floer.SphericalPeriodGroup ω c` is the class of a sphere at `x`. So the cap
classes of a contractible loop form a torsor under `Γ`
(`TauCeti.Floer.SphericalCapClass.instAddTorsor`), with
`SphericalCapClass.mk D' -ᵥ SphericalCapClass.mk D` the class of the sphere `D' -ᵥ D`. The group
`Γ` does not depend on the base point. This gives one common coefficient group acting on the
caps of all the contractible orbits of a Hamiltonian, whose based loops have different base
points. Gluing a homotopy of loops descends to cap classes
(`TauCeti.Floer.SphericalCapClass.glue`) and commutes with recapping. So does gluing along a pair
of pants (`TauCeti.Floer.SphericalCapClass.glue₂`), which is equivariant in each input: these are
the hypotheses of the product-class laws of `TauCeti.Geometry.Symplectic.Floer.Cap.Basic`, such
as `TauCeti.Floer.productClass_eq_add_sub`. The product class of the classes of caps `D₁`, `D₂`,
`D₀` is the class of the sphere `D₀ -ᵥ RawCap.glue₂ u D₁ D₂`
(`TauCeti.Floer.SphericalCapClass.productClass_glue₂_mk`). Functions on raw caps that
obey a recapping law descend to cap classes (`TauCeti.Floer.SphericalCapClass.lift`); this is how
the action and the grading of a capped orbit descend.

The torsors constructed here satisfy the hypotheses of the cap-class API of
`TauCeti.Geometry.Symplectic.Floer.Cap.Basic`, such as `TauCeti.Floer.productClass` and
`TauCeti.Floer.eq_iff_action_eq_and_index_eq`, with the abstract torsors there replaced by the
cap classes of actual loops.

## Main definitions

* `TauCeti.Floer.RawCap γ`: the homotopy classes of discs bounding the loop `γ`.
* `TauCeti.Floer.RawCap.instAddTorsor`: for a null-homotopic loop, the raw caps form a torsor under
  `π₂(X, x)`.
* `TauCeti.Floer.RawCap.glue₂`, `TauCeti.Floer.SphericalCapClass.glue₂`: gluing caps of the inputs
  of a pair of pants to a cap of its output.
* `TauCeti.Floer.SphericalCapClass ω c γ`: the cap classes of `γ` with respect to `ω` and `c`.
* `TauCeti.Floer.SphericalCapClass.instAddTorsor`: on a path-connected space, the cap classes of a
  null-homotopic loop form a torsor under the spherical period group.
* `TauCeti.Floer.SphericalCapClass.glue`: gluing a homotopy of loops to cap classes, a bijection
  `TauCeti.Floer.SphericalCapClass.glueEquiv`.
* `TauCeti.Floer.SphericalCapClass.lift`: the descent of a function on raw caps obeying a recapping
  law.

## Main results

* `TauCeti.Floer.RawCap.nonempty_iff`: a loop has a raw cap exactly when it is null-homotopic.
* `TauCeti.Floer.RawCap.comp_vadd`, `TauCeti.Floer.RawCap.comp_vsub_comp`: gluing a homotopy of
  loops commutes with gluing spheres and preserves differences of caps.
* `TauCeti.Floer.SphericalCapClass.mk_eq_mk_iff`: two raw caps have the same class exactly when
  the sphere by which they differ has zero area and zero first Chern number.
* `TauCeti.Floer.SphericalCapClass.ofHomotopyGroup_vadd_mk`,
  `TauCeti.Floer.SphericalCapClass.mk_vsub_mk`: the torsor structure on cap classes is computed on
  raw caps.
* `TauCeti.Floer.SphericalCapClass.glue_id`, `TauCeti.Floer.SphericalCapClass.glue_comp`: gluing is
  functorial in the homotopy of loops.
* `TauCeti.Floer.SphericalCapClass.glue_vadd`, `TauCeti.Floer.SphericalCapClass.glue_vsub_glue`,
  `TauCeti.Floer.SphericalCapClass.lift_vadd`: gluing and descended functions obey the recapping
  laws.
* `TauCeti.Floer.RawCap.glue₂_vadd_left`, `TauCeti.Floer.RawCap.glue₂_vadd_right`,
  `TauCeti.Floer.SphericalCapClass.glue₂_vadd_left`,
  `TauCeti.Floer.SphericalCapClass.glue₂_vadd_right`: gluing along a pair of pants is equivariant
  in each input.
* `TauCeti.Floer.SphericalCapClass.productClass_glue₂_mk`: the product class of actual caps is the
  class of the sphere by which the output cap differs from the glued cap.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524, on capped loops and the covering of the space of
  contractible loops.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology, on capped periodic orbits.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology HomotopyGroup
open scoped Topology Topology.Homotopy

namespace TauCeti.Floer

section Raw

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The **raw caps** of a loop `γ` based at `x`: the homotopy classes, relative to the endpoints,
of paths in the loop space `Ω X x` from `γ` to the constant loop. Such a path `s ↦ D_s` is a disc
`(s, t) ↦ D_s t` bounding `γ`, and its homotopy class is the class of the disc relative to its
boundary. They are the morphisms from `γ` to the constant loop in the fundamental groupoid of
`Ω X x`; it is an abbreviation so that the groupoid structure applies to raw caps directly. In
particular a homotopy of loops `p` from `γ₁` to `γ₂`, which is a cylinder whose seam stays at `x`,
glues to a raw cap `D` of `γ₂` to give the raw cap `p ≫ D` of `γ₁`. -/
abbrev RawCap (γ : Ω X x) : Type _ :=
  (⟨γ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨Path.refl x⟩

namespace RawCap

variable {γ γ₀ γ₁ γ₂ : Ω X x}

/-- **A loop has a raw cap exactly when it is null-homotopic.** -/
theorem nonempty_iff : Nonempty (RawCap γ) ↔ γ.Homotopic (Path.refl x) := by
  rw [← Path.joined_iff_homotopic]
  exact ⟨fun ⟨D⟩ => ⟨D.out⟩, fun ⟨D⟩ => ⟨Path.Homotopic.Quotient.mk D⟩⟩

/-- Gluing a sphere `a ∈ π₂(X, x)` at the centre of a disc: `a +ᵥ D` is `D` followed by the loop
of loops at the constant loop corresponding to `a`. -/
instance instAddAction : AddAction (Additive (π_ 2 X x)) (RawCap γ) where
  vadd a D := fundamentalGroupLoopSpaceMulEquiv.symm a.toMul • D
  -- unfold `+ᵥ` to the action of the vertex group by postcomposition
  zero_vadd D := by
    change fundamentalGroupLoopSpaceMulEquiv.symm (Additive.toMul 0) • D = D
    rw [toMul_zero, _root_.map_one, one_smul]
  add_vadd a b D := by
    change fundamentalGroupLoopSpaceMulEquiv.symm (Additive.toMul (a + b)) • D = _ • _ • D
    rw [toMul_add, _root_.map_mul, mul_smul]

theorem vadd_def (a : Additive (π_ 2 X x)) (D : RawCap γ) :
    a +ᵥ D = D ≫ (fundamentalGroupLoopSpaceMulEquiv.symm a.toMul).asHom :=
  (rfl)

/-- The sphere `D' -ᵥ D` by which two raw caps differ: `D` run backwards, followed by `D'`. -/
instance instVSub : VSub (Additive (π_ 2 X x)) (RawCap γ) where
  vsub D' D := .ofMul <| fundamentalGroupLoopSpaceMulEquiv (D' /ₛ D)

theorem vsub_def (D' D : RawCap γ) :
    D' -ᵥ D = .ofMul (fundamentalGroupLoopSpaceMulEquiv (D' /ₛ D)) :=
  (rfl)

/-- **The raw caps of a contractible loop form a torsor under `π₂(X, x)`.** Any two discs bounding
`γ` differ by a unique sphere glued at the centre. -/
instance instAddTorsor [Nonempty (RawCap γ)] : AddTorsor (Additive (π_ 2 X x)) (RawCap γ) where
  vsub_vadd' D' D := by
    rw [vadd_def, vsub_def, toMul_ofMul, MulEquiv.symm_apply_apply, ← End.smul_right, sdiv_smul]
  vadd_vsub' a D := by
    rw [vadd_def, vsub_def, ← End.smul_right, smul_sdiv, MulEquiv.apply_symm_apply, ofMul_toMul]

/-- Gluing a homotopy of loops to a cap commutes with gluing spheres at the centre. -/
@[simp]
theorem comp_vadd (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) (a : Additive (π_ 2 X x))
    (D : RawCap γ₂) : p ≫ (a +ᵥ D) = a +ᵥ (p ≫ D) := by
  simp only [vadd_def, Category.assoc]

/-- Gluing a homotopy of loops to caps preserves the sphere by which they differ. -/
@[simp]
theorem comp_vsub_comp (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (D' D : RawCap γ₂) : (p ≫ D' : RawCap γ₁) -ᵥ (p ≫ D) = D' -ᵥ D := by
  have : Nonempty (RawCap γ₁) := ⟨p ≫ D⟩
  have : Nonempty (RawCap γ₂) := ⟨D⟩
  have h := vadd_vsub (D' -ᵥ D) (p ≫ D : RawCap γ₁)
  rwa [← comp_vadd, vsub_vadd] at h

/-- **Gluing caps along a pair of pants.** A homotopy of loops `u` from `γ₀` to the concatenation
`γ₁.trans γ₂`, a pair of pants with inputs `γ₁`, `γ₂` and output `γ₀`, glues raw caps `D₁` of
`γ₁` and `D₂` of `γ₂` to a raw cap of `γ₀`: follow `u`, then concatenate `D₁` and `D₂` pointwise
in the loop space, ending at the concatenation of the constant loop with itself, which is the
constant loop. -/
def glue₂ (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁)
    (D₂ : RawCap γ₂) : RawCap γ₀ :=
  u ≫ ((Path.Homotopic.prod D₁ D₂).map
    ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast rfl
      Path.refl_trans_refl.symm

theorem glue₂_def (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    glue₂ u D₁ D₂ = u ≫ ((Path.Homotopic.prod D₁ D₂).map
      ⟨fun ρ : Path x x × Path x x => ρ.1.trans ρ.2, Path.continuous_trans⟩).cast rfl
        Path.refl_trans_refl.symm :=
  (rfl)

/-- Gluing a sphere to the cap of the first input of a pair of pants glues it to the glued cap of
the output. -/
@[simp]
theorem glue₂_vadd_left (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    glue₂ u (a +ᵥ D₁) D₂ = a +ᵥ glue₂ u D₁ D₂ := by
  rw [vadd_def, vadd_def, glue₂_def, glue₂_def]
  refine (congrArg (u ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  conv_lhs => rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.trans_refl D₂,
    ← Path.Homotopic.comp_prod_eq_prod_comp,
    Path.Homotopic.Quotient.map_trans_cast _ _ rfl Path.refl_trans_refl.symm
      Path.refl_trans_refl.symm]
  exact congrArg _ (Path.Homotopic.Quotient.cast_map_trans_prod_refl _)

/-- Gluing a sphere to the cap of the second input of a pair of pants glues it to the glued cap
of the output. -/
@[simp]
theorem glue₂_vadd_right (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (a : Additive (π_ 2 X x)) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    glue₂ u D₁ (a +ᵥ D₂) = a +ᵥ glue₂ u D₁ D₂ := by
  rw [vadd_def, vadd_def, glue₂_def, glue₂_def]
  refine (congrArg (u ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  conv_lhs => rw [FundamentalGroupoid.comp_eq, ← Path.Homotopic.Quotient.trans_refl D₁,
    ← Path.Homotopic.comp_prod_eq_prod_comp,
    Path.Homotopic.Quotient.map_trans_cast _ _ rfl Path.refl_trans_refl.symm
      Path.refl_trans_refl.symm]
  exact congrArg _ (Path.Homotopic.Quotient.cast_map_trans_refl_prod _)

end RawCap

end Raw

section Spherical

variable {X : Type} [TopologicalSpace X] {x : X}

variable (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℝ)
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of X) →+ ℤ)

/-- The **cap classes** of a loop `γ` based at `x`, with respect to homomorphisms `ω` and `c` on
`H₂(X; ℤ)` (for a symplectic manifold, the symplectic area and the first Chern number): the raw
caps of `γ` modulo gluing spheres whose Hurewicz classes have zero area and zero first Chern
number. On a path-connected space, the cap classes of a null-homotopic loop form a torsor under
`SphericalPeriodGroup ω c`. -/
@[expose] def SphericalCapClass (γ : Ω X x) : Type :=
  AddAction.orbitRel.Quotient (SphericalPeriodGroup.ofHomotopyGroup ω c x).ker (RawCap γ)

namespace SphericalCapClass

variable {ω c} {γ γ₀ γ₁ γ₂ : Ω X x}

variable (ω c) in
/-- The cap class of a raw cap. -/
def mk (D : RawCap γ) : SphericalCapClass ω c γ :=
  Quotient.mk'' D

theorem mk_surjective : Function.Surjective (mk ω c : RawCap γ → SphericalCapClass ω c γ) :=
  Quotient.mk''_surjective

@[elab_as_elim]
theorem induction_on {motive : SphericalCapClass ω c γ → Prop} (q : SphericalCapClass ω c γ)
    (h : ∀ D, motive (mk ω c D)) : motive q :=
  Quotient.inductionOn' q h

/-- Two raw caps of a contractible loop have the same cap class exactly when the sphere by which
they differ has zero area and zero first Chern number. -/
theorem mk_eq_mk_iff {D D' : RawCap γ} :
    mk ω c D = mk ω c D' ↔
      ω (hurewiczIntHom X x 1 (D -ᵥ D')) = 0 ∧ c (hurewiczIntHom X x 1 (D -ᵥ D')) = 0 := by
  have : Nonempty (RawCap γ) := ⟨D⟩
  refine Quotient.eq''.trans <| (AddAction.orbitRel.Quotient.orbitRel_iff_vsub_mem _).trans ?_
  rw [AddMonoidHom.mem_ker, PeriodGroup.ext_iff]
  simp

/-- The class of the period group by which two cap classes differ: the class of the sphere by
which representatives differ. -/
instance instVSub : VSub (SphericalPeriodGroup ω c) (SphericalCapClass ω c γ) where
  vsub q' q := Quotient.liftOn₂' q' q
    (fun D' D => SphericalPeriodGroup.ofHomotopyGroup ω c x (D' -ᵥ D))
    fun D₁ D₂ D₁' D₂' h h' => by
      have : Nonempty (RawCap γ) := ⟨D₁⟩
      simpa only [QuotientAddGroup.kerLift_mk] using
        congrArg (QuotientAddGroup.kerLift (SphericalPeriodGroup.ofHomotopyGroup ω c x))
          (AddAction.orbitRel.Quotient.mk_vsub_eq_mk_vsub _ h h')

/-- Two cap classes differ by the class of the sphere by which their representatives differ. -/
@[simp]
theorem mk_vsub_mk (D' D : RawCap γ) :
    mk ω c D' -ᵥ mk ω c D = SphericalPeriodGroup.ofHomotopyGroup ω c x (D' -ᵥ D) :=
  (rfl)

variable {A : Type*} [AddMonoid A]

/-- The descent to cap classes of a function `f` on raw caps obeying the recapping law
`f (a +ᵥ D) = φ [a] + f D` for a homomorphism `φ` on the period group, where `[a]` is the class of
the sphere `a`. The action and the grading of a capped orbit are of this form. -/
def lift (φ : SphericalPeriodGroup ω c →+ A) (f : RawCap γ → A)
    (hf : ∀ a D, f (a +ᵥ D) = φ (SphericalPeriodGroup.ofHomotopyGroup ω c x a) + f D) :
    SphericalCapClass ω c γ → A :=
  Quotient.lift (s := AddAction.orbitRel _ _) f fun D D' ⟨k, hk⟩ => by
    rw [← hk]
    simp only [AddSubgroup.vadd_def, hf, AddMonoidHom.mem_ker.1 k.2, map_zero, zero_add]

@[simp]
theorem lift_mk (φ : SphericalPeriodGroup ω c →+ A) (f : RawCap γ → A)
    (hf : ∀ a D, f (a +ᵥ D) = φ (SphericalPeriodGroup.ofHomotopyGroup ω c x a) + f D)
    (D : RawCap γ) : lift φ f hf (mk ω c D) = f D :=
  (rfl)

/-- Gluing a homotopy of loops `p` from `γ₁` to `γ₂` to cap classes of `γ₂` gives cap classes of
`γ₁`, computed on representatives by composition in the fundamental groupoid of the loop
space. -/
def glue (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    SphericalCapClass ω c γ₂ → SphericalCapClass ω c γ₁ :=
  Quotient.map' (p ≫ ·) fun _ D' ⟨k, hk⟩ =>
    ⟨k, by simp only [← hk, AddSubgroup.vadd_def, RawCap.comp_vadd]⟩

@[simp]
theorem glue_mk (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) (D : RawCap γ₂) :
    glue p (mk ω c D) = mk ω c (p ≫ D) :=
  (rfl)

/-- Gluing the constant homotopy of loops does nothing. -/
@[simp]
theorem glue_id (q : SphericalCapClass ω c γ) : glue (𝟙 _) q = q := by
  induction q using induction_on with
  | h D => rw [glue_mk, Category.id_comp]

/-- Gluing a composite homotopy of loops is gluing one after the other. -/
@[simp]
theorem glue_comp {γ₃ : Ω X x} (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (p' : (⟨γ₂⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₃⟩) (q : SphericalCapClass ω c γ₃) :
    glue (p ≫ p') q = glue p (glue p' q) := by
  induction q using induction_on with
  | h D => rw [glue_mk, glue_mk, glue_mk, Category.assoc]

/-- Gluing a homotopy of loops `p` from `γ₁` to `γ₂` is a bijection from the cap classes of `γ₂`
to those of `γ₁`, with inverse gluing the reversed homotopy. -/
@[expose, simps]
def glueEquiv (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩) :
    SphericalCapClass ω c γ₂ ≃ SphericalCapClass ω c γ₁ where
  toFun := glue p
  invFun := glue (inv p)
  left_inv q := by rw [← glue_comp, IsIso.inv_hom_id, glue_id]
  right_inv q := by rw [← glue_comp, IsIso.hom_inv_id, glue_id]

/-- Gluing a homotopy preserves the class by which two cap classes differ. -/
@[simp]
theorem glue_vsub_glue (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (q' q : SphericalCapClass ω c γ₂) :
    glue p q' -ᵥ glue p q = q' -ᵥ q := by
  induction q' using induction_on with | h D' =>
  induction q using induction_on with
  | h D => rw [glue_mk, glue_mk, mk_vsub_mk, mk_vsub_mk, RawCap.comp_vsub_comp]

/-- **Gluing cap classes along a pair of pants.** A homotopy of loops `u` from `γ₀` to
`γ₁.trans γ₂` glues cap classes of `γ₁` and `γ₂` to a cap class of `γ₀`, computed on
representatives by `TauCeti.Floer.RawCap.glue₂`. -/
def glue₂ (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) :
    SphericalCapClass ω c γ₁ → SphericalCapClass ω c γ₂ → SphericalCapClass ω c γ₀ :=
  Quotient.map₂ (RawCap.glue₂ u) fun _ D₁ ⟨k₁, hk₁⟩ _ D₂ ⟨k₂, hk₂⟩ =>
    ⟨k₂ + k₁, by simp only [← hk₁, ← hk₂, AddSubgroup.vadd_def, RawCap.glue₂_vadd_left,
      RawCap.glue₂_vadd_right, add_vadd]⟩

@[simp]
theorem glue₂_mk (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (D₁ : RawCap γ₁) (D₂ : RawCap γ₂) :
    glue₂ u (mk ω c D₁) (mk ω c D₂) = mk ω c (RawCap.glue₂ u D₁ D₂) :=
  (rfl)

variable [PathConnectedSpace X]

/-- Recapping a cap class by a class of the period group: `[a] +ᵥ mk D = mk (a +ᵥ D)` for any
sphere `a`, where `[a]` is its class. It is the action of the quotient of `π₂(X, x)` on the orbit
space, transported along the first isomorphism theorem for the surjection
`SphericalPeriodGroup.ofHomotopyGroup`. -/
instance instAddAction : AddAction (SphericalPeriodGroup ω c) (SphericalCapClass ω c γ) :=
  AddAction.compHom (AddAction.orbitRel.Quotient
      (SphericalPeriodGroup.ofHomotopyGroup ω c x).ker (RawCap γ))
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (SphericalPeriodGroup.ofHomotopyGroup_surjective x)).symm.toAddMonoidHom

/-- Recapping by the class of a sphere `a` is gluing `a` to a representative. -/
@[simp]
theorem ofHomotopyGroup_vadd_mk (a : Additive (π_ 2 X x)) (D : RawCap γ) :
    SphericalPeriodGroup.ofHomotopyGroup ω c x a +ᵥ mk ω c D = mk ω c (a +ᵥ D) := by
  -- the action is that of the quotient group on the orbit space, after transport along the
  -- inverse of the first isomorphism theorem
  exact (congrArg (· +ᵥ (Quotient.mk'' D : AddAction.orbitRel.Quotient _ (RawCap γ)))
    (TauCeti.QuotientAddGroup.quotientKerEquivOfSurjective_symm_apply _
      (SphericalPeriodGroup.ofHomotopyGroup_surjective x) a)).trans
    (AddAction.orbitRel.Quotient.mk_vadd_mk _ a D)

/-- **The cap classes of a contractible loop form a torsor under the spherical period group**, on
a path-connected space. -/
instance instAddTorsor [Nonempty (RawCap γ)] :
    AddTorsor (SphericalPeriodGroup ω c) (SphericalCapClass ω c γ) where
  nonempty := ⟨mk ω c (Classical.arbitrary _)⟩
  vsub_vadd' q' q := by
    induction q' using induction_on with | h D' =>
    induction q using induction_on with
    | h D => rw [mk_vsub_mk, ofHomotopyGroup_vadd_mk, vsub_vadd]
  vadd_vsub' g q := by
    obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
    induction q using induction_on with
    | h D => rw [ofHomotopyGroup_vadd_mk, mk_vsub_mk, vadd_vsub]

/-- Gluing a homotopy commutes with recapping. -/
@[simp]
theorem glue_vadd (p : (⟨γ₁⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₂⟩)
    (g : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ₂) :
    glue p (g +ᵥ q) = g +ᵥ glue p q := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q using induction_on with
  | h D => rw [ofHomotopyGroup_vadd_mk, glue_mk, glue_mk, ofHomotopyGroup_vadd_mk,
      RawCap.comp_vadd]

/-- Recapping the first input of a pair of pants recaps the glued output by the same class. -/
@[simp]
theorem glue₂_vadd_left (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (g : SphericalPeriodGroup ω c)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂) :
    glue₂ u (g +ᵥ q₁) q₂ = g +ᵥ glue₂ u q₁ q₂ := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [ofHomotopyGroup_vadd_mk, glue₂_mk, glue₂_mk, ofHomotopyGroup_vadd_mk,
      RawCap.glue₂_vadd_left]

/-- Recapping the second input of a pair of pants recaps the glued output by the same class. -/
@[simp]
theorem glue₂_vadd_right (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩)
    (g : SphericalPeriodGroup ω c)
    (q₁ : SphericalCapClass ω c γ₁) (q₂ : SphericalCapClass ω c γ₂) :
    glue₂ u q₁ (g +ᵥ q₂) = g +ᵥ glue₂ u q₁ q₂ := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q₁ using induction_on with | h D₁ =>
  induction q₂ using induction_on with
  | h D₂ => rw [ofHomotopyGroup_vadd_mk, glue₂_mk, glue₂_mk, ofHomotopyGroup_vadd_mk,
      RawCap.glue₂_vadd_right]

/-- The class `A = D₀ + u − D₁ − D₂` of a pair of pants `u` relative to caps `D₁`, `D₂` of its
inputs and `D₀` of its output is the class of the sphere `D₀ -ᵥ RawCap.glue₂ u D₁ D₂` by which
the output cap differs from the glued cap. -/
@[simp]
theorem productClass_glue₂_mk [Nonempty (RawCap γ₀)]
    (u : (⟨γ₀⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨γ₁.trans γ₂⟩) (D₁ : RawCap γ₁) (D₂ : RawCap γ₂)
    (D₀ : RawCap γ₀) :
    productClass (ω := ω.comp (sphericalClasses X 1).subtype)
        (c := c.comp (sphericalClasses X 1).subtype) (glue₂ u) (mk ω c D₁) (mk ω c D₂)
        (mk ω c D₀) =
      SphericalPeriodGroup.ofHomotopyGroup ω c x (D₀ -ᵥ RawCap.glue₂ u D₁ D₂) := by
  rw [productClass_def, glue₂_mk, mk_vsub_mk]

/-- The descended function obeys the recapping law on cap classes. -/
@[simp]
theorem lift_vadd (φ : SphericalPeriodGroup ω c →+ A) (f : RawCap γ → A)
    (hf : ∀ a D, f (a +ᵥ D) = φ (SphericalPeriodGroup.ofHomotopyGroup ω c x a) + f D)
    (g : SphericalPeriodGroup ω c) (q : SphericalCapClass ω c γ) :
    lift φ f hf (g +ᵥ q) = φ g + lift φ f hf q := by
  obtain ⟨a, rfl⟩ := SphericalPeriodGroup.ofHomotopyGroup_surjective (ω := ω) (c := c) x g
  induction q using induction_on with
  | h D => rw [ofHomotopyGroup_vadd_mk, lift_mk, lift_mk, hf]

end SphericalCapClass

end Spherical

end TauCeti.Floer
