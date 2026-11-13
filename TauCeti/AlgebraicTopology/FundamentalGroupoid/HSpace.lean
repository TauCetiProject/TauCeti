/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HSpaces
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Products of path classes in an H-space

An H-space `Y` carries a continuous multiplication `hmul : Y × Y → Y`, written `y₁ ⋀ y₂`, with a
neutral element `e` up to homotopies `eHmul` and `hmulE` relative to `e`
(`HSpace` in Mathlib). Multiplying two paths pointwise gives a path between the products of their
endpoints, and this descends to homotopy classes: for morphisms `p : a₁ ⟶ b₁` and `q : a₂ ⟶ b₂`
of the fundamental groupoid of `Y`, `HSpace.pathHmul p q : a₁ ⋀ a₂ ⟶ b₁ ⋀ b₂` is the class of
`t ↦ p t ⋀ q t`. It is functorial (`HSpace.pathHmul_id`, `HSpace.pathHmul_comp`).

Multiplying by the identity of `e` is conjugation by the traces of the unit homotopies
(`HSpace.pathHmul_id_left_comp_evalAt_eHmul`, `HSpace.pathHmul_id_right_comp_evalAt_hmulE`):
this is the naturality of the isomorphism of induced functors given by a homotopy
(`FundamentalGroupoidFunctor.homotopicMapsNatIso`). Since the unit homotopies are relative to
`e`, their traces at `e` are constant, so on loops at `e` the product with the identity of `e` is
the loop itself, transported along `e ⋀ e = e`
(`HSpace.pathHmul_id_left_comp_eqToHom`, `HSpace.pathHmul_id_right_comp_eqToHom`).

Multiplying a path class `p : a ⟶ b` on the left by a loop class `ℓ` at `e`, and reading the
product `ℓ ⋀ p : e ⋀ a ⟶ e ⋀ b` back through the traces of `eHmul`, gives a path class
`HSpace.loopHmul ℓ p : a ⟶ b` with the same endpoints. This is a left action of the loops at `e`
on the path classes between any two points (`HSpace.loopHmul_id`, `HSpace.loopHmul_loopHmul`),
commuting with composition on both sides (`HSpace.loopHmul_comp`, `HSpace.comp_loopHmul`). On a
path class `D` from `a` to `e` it is postcomposition with `ℓ` (`HSpace.loopHmul_eq_comp_loop`),
and in general it is precomposition with the loop `D ≫ ℓ ≫ D⁻¹` at `a`, for any such `D`
(`HSpace.loopHmul_eq_comp_comp_inv_comp`).

The main example is the loop space `Ω X x = Path x x`, with concatenation of loops and the
constant loop. A path in `Ω X x` from a loop `γ` to the constant loop is a disc bounding `γ`, and
`pathHmul` places two such discs side by side; the unit laws say that placing the constant disc
beside a sphere at the constant loop does not change the sphere. For a loop class `ℓ` at the
constant loop, that is a sphere, `loopHmul ℓ p` places the sphere beside a homotopy of loops `p`:
it glues the sphere to the cylinder `p`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. (2) **54**
  (1951), 425–505, on H-spaces and the loop space.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.C, on H-spaces.
-/

public section

noncomputable section

open CategoryTheory
open scoped HSpaces

namespace HSpace

variable {Y : Type*} [TopologicalSpace Y] [HSpace Y]

/-- The product of two path classes in an H-space: the class of the pointwise product
`t ↦ p t ⋀ q t` of representatives, a path from `a₁ ⋀ a₂` to `b₁ ⋀ b₂`. -/
def pathHmul {a₁ b₁ a₂ b₂ : Y} (p : (⟨a₁⟩ : FundamentalGroupoid Y) ⟶ ⟨b₁⟩)
    (q : (⟨a₂⟩ : FundamentalGroupoid Y) ⟶ ⟨b₂⟩) :
    (⟨a₁ ⋀ a₂⟩ : FundamentalGroupoid Y) ⟶ ⟨b₁ ⋀ b₂⟩ :=
  (Path.Homotopic.prod p q).map hmul

/-- The product of the classes of two paths is the class of their pointwise product. -/
theorem pathHmul_mk {a₁ b₁ a₂ b₂ : Y} (p : Path a₁ b₁) (q : Path a₂ b₂) :
    pathHmul (Path.Homotopic.Quotient.mk p : (⟨a₁⟩ : FundamentalGroupoid Y) ⟶ ⟨b₁⟩)
        (Path.Homotopic.Quotient.mk q : (⟨a₂⟩ : FundamentalGroupoid Y) ⟶ ⟨b₂⟩) =
      Path.Homotopic.Quotient.mk ((p.prod q).map hmul.continuous) :=
  (rfl)

/-- The product of two identities is an identity. -/
@[simp]
theorem pathHmul_id (a b : Y) :
    pathHmul (𝟙 (⟨a⟩ : FundamentalGroupoid Y)) (𝟙 (⟨b⟩ : FundamentalGroupoid Y)) = 𝟙 _ := by
  rw [FundamentalGroupoid.id_eq_path_refl, FundamentalGroupoid.id_eq_path_refl,
    FundamentalGroupoid.id_eq_path_refl]
  exact congrArg Path.Homotopic.Quotient.mk (Path.ext rfl)

/-- **The product of path classes is functorial**: the product of two composites is the composite
of the products. -/
@[reassoc]
theorem pathHmul_comp {a₁ b₁ c₁ a₂ b₂ c₂ : Y} (p : (⟨a₁⟩ : FundamentalGroupoid Y) ⟶ ⟨b₁⟩)
    (p' : (⟨b₁⟩ : FundamentalGroupoid Y) ⟶ ⟨c₁⟩) (q : (⟨a₂⟩ : FundamentalGroupoid Y) ⟶ ⟨b₂⟩)
    (q' : (⟨b₂⟩ : FundamentalGroupoid Y) ⟶ ⟨c₂⟩) :
    pathHmul (p ≫ p') (q ≫ q') = pathHmul p q ≫ pathHmul p' q' := by
  rw [pathHmul, pathHmul, pathHmul, FundamentalGroupoid.comp_eq, FundamentalGroupoid.comp_eq,
    ← Path.Homotopic.comp_prod_eq_prod_comp]
  exact (FundamentalGroupoid.map hmul).map_comp
    (X := ⟨(a₁, a₂)⟩) (Y := ⟨(b₁, b₂)⟩) (Z := ⟨(c₁, c₂)⟩)
    (Path.Homotopic.prod p q) (Path.Homotopic.prod p' q')

/-- **Left multiplication by the neutral element, on path classes.** For a path class
`p : a ⟶ b`, the product `𝟙 e ⋀ p : e ⋀ a ⟶ e ⋀ b` is `p` conjugated by the traces at `a` and `b`
of the left unit homotopy `eHmul` from `y ↦ e ⋀ y` to the identity. -/
theorem pathHmul_id_left_comp_evalAt_eHmul {a b : Y} (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    pathHmul (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) p ≫
        (⟦eHmul.evalAt b⟧ : (⟨e ⋀ b⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) =
      (⟦eHmul.evalAt a⟧ : (⟨e ⋀ a⟩ : FundamentalGroupoid Y) ⟶ ⟨a⟩) ≫ p := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso eHmul.toHomotopy).naturality p
  simp only [FundamentalGroupoidFunctor.homotopicMapsNatIso_app, FundamentalGroupoid.map_map,
    ContinuousMap.coe_id] at h
  -- `h` is stated with `Path.Homotopic.Quotient.map`, defined by `Quotient.map`: on a
  -- representative path, `pathHmul (𝟙 e) p` and the image of `p` under `y ↦ e ⋀ y` are both the
  -- class of `t ↦ e ⋀ p t`, and the image of `p` under the identity is `p`. These agree
  -- definitionally only once a representative is chosen.
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => exact h

/-- **Right multiplication by the neutral element, on path classes.** For a path class
`p : a ⟶ b`, the product `p ⋀ 𝟙 e : a ⋀ e ⟶ b ⋀ e` is `p` conjugated by the traces at `a` and `b`
of the right unit homotopy `hmulE` from `y ↦ y ⋀ e` to the identity. -/
theorem pathHmul_id_right_comp_evalAt_hmulE {a b : Y} (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    pathHmul p (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) ≫
        (⟦hmulE.evalAt b⟧ : (⟨b ⋀ e⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) =
      (⟦hmulE.evalAt a⟧ : (⟨a ⋀ e⟩ : FundamentalGroupoid Y) ⟶ ⟨a⟩) ≫ p := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso hmulE.toHomotopy).naturality p
  simp only [FundamentalGroupoidFunctor.homotopicMapsNatIso_app, FundamentalGroupoid.map_map,
    ContinuousMap.coe_id] at h
  -- As in `pathHmul_id_left_comp_evalAt_eHmul`, the two sides of `h` agree with the goal
  -- definitionally only once a representative of `p` is chosen.
  induction p using Path.Homotopic.Quotient.ind with
  | mk p => exact h

/-- The trace at `e` of the left unit homotopy is the constant path, transported along
`e ⋀ e = e`, since the homotopy is relative to `e`. -/
theorem mk_evalAt_eHmul_e :
    FundamentalGroupoid.fromPath ⟦(eHmul (X := Y)).evalAt e⟧ =
      eqToHom (congrArg FundamentalGroupoid.mk (hmul_e_e (X := Y))) := by
  rw [FundamentalGroupoid.eqToHom_eq hmul_e_e]
  refine congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t => ?_))
  exact (eHmul.eq_fst t rfl).trans hmul_e_e

/-- The trace at `e` of the right unit homotopy is the constant path, transported along
`e ⋀ e = e`, since the homotopy is relative to `e`. -/
theorem mk_evalAt_hmulE_e :
    FundamentalGroupoid.fromPath ⟦(hmulE (X := Y)).evalAt e⟧ =
      eqToHom (congrArg FundamentalGroupoid.mk (hmul_e_e (X := Y))) := by
  rw [FundamentalGroupoid.eqToHom_eq hmul_e_e]
  refine congrArg Path.Homotopic.Quotient.mk (Path.ext (funext fun t => ?_))
  exact (hmulE.eq_fst t rfl).trans hmul_e_e

/-- **The identity of `e` is a left unit for loops at `e`**: for a loop class `p` at `e`, the
product `𝟙 e ⋀ p` is `p`, transported along `e ⋀ e = e`. -/
@[reassoc]
theorem pathHmul_id_left_comp_eqToHom (p : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) :
    pathHmul (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) p ≫
        eqToHom (congrArg FundamentalGroupoid.mk hmul_e_e) =
      eqToHom (congrArg FundamentalGroupoid.mk hmul_e_e) ≫ p := by
  rw [← mk_evalAt_eHmul_e]
  exact pathHmul_id_left_comp_evalAt_eHmul p

/-- **The identity of `e` is a right unit for loops at `e`**: for a loop class `p` at `e`, the
product `p ⋀ 𝟙 e` is `p`, transported along `e ⋀ e = e`. -/
@[reassoc]
theorem pathHmul_id_right_comp_eqToHom (p : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) :
    pathHmul p (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) ≫
        eqToHom (congrArg FundamentalGroupoid.mk hmul_e_e) =
      eqToHom (congrArg FundamentalGroupoid.mk hmul_e_e) ≫ p := by
  rw [← mk_evalAt_hmulE_e]
  exact pathHmul_id_right_comp_evalAt_hmulE p

/-! ### Left multiplication by loops at the neutral element -/

/-- The trace at `a` of the left unit homotopy `eHmul`, a path class from `e ⋀ a` to `a`. -/
private def eHmulTrace (a : Y) : (⟨e ⋀ a⟩ : FundamentalGroupoid Y) ⟶ ⟨a⟩ :=
  ⟦eHmul.evalAt a⟧

private theorem pathHmul_id_left_comp_eHmulTrace {a b : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    pathHmul (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) p ≫ eHmulTrace b = eHmulTrace a ≫ p :=
  pathHmul_id_left_comp_evalAt_eHmul p

private theorem eHmulTrace_e :
    eHmulTrace (e : Y) = eqToHom (congrArg FundamentalGroupoid.mk hmul_e_e) :=
  mk_evalAt_eHmul_e

private theorem inv_eHmulTrace_comp_pathHmul_id_left {a b : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    inv (eHmulTrace a) ≫ pathHmul (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) p = p ≫ inv (eHmulTrace b) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, pathHmul_id_left_comp_eHmulTrace]

/-- **Left multiplication of a path class by a loop at the neutral element.** For a loop class
`ℓ` at `e` and a path class `p : a ⟶ b`, the product `ℓ ⋀ p : e ⋀ a ⟶ e ⋀ b`, read back as a path
class from `a` to `b` through the traces at `a` and `b` of the left unit homotopy `eHmul`. For the
identity of `e` it is `p` itself (`HSpace.loopHmul_id`); it is a left action of the loops at `e`
on the path classes between any two points (`HSpace.loopHmul_loopHmul`), commuting with
composition on either side (`HSpace.loopHmul_comp`, `HSpace.comp_loopHmul`). -/
def loopHmul (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩ :=
  inv (eHmulTrace a) ≫ pathHmul ℓ p ≫ eHmulTrace b

theorem loopHmul_def (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    loopHmul ℓ p = inv (FundamentalGroupoid.fromPath ⟦eHmul.evalAt a⟧) ≫ pathHmul ℓ p ≫
      FundamentalGroupoid.fromPath ⟦eHmul.evalAt b⟧ :=
  (rfl)

/-- Left multiplication by the identity of `e` does not change a path class. -/
@[simp]
theorem loopHmul_id {a b : Y} (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    loopHmul (𝟙 _) p = p := by
  rw [loopHmul, pathHmul_id_left_comp_eHmulTrace, IsIso.inv_hom_id_assoc]

/-- Left multiplication by a loop commutes with postcomposition. -/
@[reassoc]
theorem loopHmul_comp (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b c : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) (q : (⟨b⟩ : FundamentalGroupoid Y) ⟶ ⟨c⟩) :
    loopHmul ℓ (p ≫ q) = loopHmul ℓ p ≫ q := by
  have h := pathHmul_comp ℓ (𝟙 _) p q
  rw [Category.comp_id] at h
  simp only [loopHmul, h, Category.assoc, pathHmul_id_left_comp_eHmulTrace]

/-- Left multiplication by a loop commutes with precomposition. -/
@[reassoc]
theorem comp_loopHmul (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b c : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) (q : (⟨b⟩ : FundamentalGroupoid Y) ⟶ ⟨c⟩) :
    p ≫ loopHmul ℓ q = loopHmul ℓ (p ≫ q) := by
  have h := pathHmul_comp (𝟙 _) ℓ p q
  rw [Category.id_comp] at h
  simp only [loopHmul, h, ← Category.assoc, inv_eHmulTrace_comp_pathHmul_id_left]

/-- Left multiplication by a loop `ℓ` of a path class ending at `e` is postcomposition with `ℓ`. -/
@[reassoc]
theorem loopHmul_eq_comp_loop (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) : loopHmul ℓ p = p ≫ ℓ := by
  have h₁ : loopHmul ℓ (𝟙 (⟨e⟩ : FundamentalGroupoid Y)) = ℓ := by
    rw [loopHmul, IsIso.inv_comp_eq, eHmulTrace_e]
    exact pathHmul_id_right_comp_eqToHom ℓ
  rw [← Category.comp_id p, ← comp_loopHmul, h₁, Category.comp_id]

/-- Left multiplication by a loop `ℓ` of a path class starting at `e` is precomposition with
`ℓ`. -/
@[reassoc]
theorem loopHmul_eq_loop_comp (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {b : Y}
    (p : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) : loopHmul ℓ p = ℓ ≫ p := by
  rw [← Category.id_comp p, loopHmul_comp, loopHmul_eq_comp_loop, Category.id_comp,
    Category.id_comp]

/-- **Left multiplication by loops is an action**: multiplying by `ℓ'` and then by `ℓ` is
multiplying by the composite loop `ℓ' ≫ ℓ`. -/
theorem loopHmul_loopHmul (ℓ ℓ' : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b : Y}
    (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    loopHmul ℓ (loopHmul ℓ' p) = loopHmul (ℓ' ≫ ℓ) p := by
  have h := pathHmul_comp ℓ' ℓ p (𝟙 _)
  rw [Category.comp_id] at h
  rw [← Category.comp_id (loopHmul ℓ' p), ← comp_loopHmul]
  simp only [loopHmul, h, Category.assoc, IsIso.hom_inv_id_assoc]

/-- **Left multiplication by a loop is conjugation along any path to `e`.** If `D` is a path class
from `a` to `e`, then multiplying a path class `p` starting at `a` by the loop `ℓ` is precomposing
`p` with the loop `D ≫ ℓ ≫ D⁻¹` at `a`. -/
@[reassoc]
theorem loopHmul_eq_comp_comp_inv_comp (ℓ : (⟨e⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) {a b : Y}
    (D : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨e⟩) (p : (⟨a⟩ : FundamentalGroupoid Y) ⟶ ⟨b⟩) :
    loopHmul ℓ p = D ≫ ℓ ≫ inv D ≫ p := by
  conv_lhs => rw [← IsIso.hom_inv_id_assoc D p]
  rw [← comp_loopHmul, loopHmul_eq_loop_comp]

end HSpace
