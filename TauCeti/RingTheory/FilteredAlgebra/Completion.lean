/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Completion of a ring along an ideal filtration

The completion of a decreasing ideal filtration is the subring of compatible
families in the quotients by its positive-order terms. Order `k` retains the
quotient by the ideal at `k + 1`. Projections, the canonical map, and lifts of
compatible families of ring homomorphisms exhibit this ring as the inverse limit.

Its induced filtration consists, in positive order, of the kernels of the
projections. It is multiplicative and separated, and the canonical map pulls it
back to the original filtration. Elements of the first completion ideal have
nilpotent projections at every finite order, with an explicit vanishing power.

The carrier uses Mathlib's `RingCat.sectionsSubring`; the transition maps use
`Ideal.Quotient.factor`. No commutativity or separatedness is assumed.

Adapted from `yuma-mizuno-lean/Mei`, commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f`,
`Mei/RingTheory/FilteredAlgebra/Completion.lean` (Apache 2.0).
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgFiltration

variable {A : Type*} [Ring A] (F : TauCeti.AlgFiltration A)

/-- The tower retaining order `k`, hence quotienting by the ideal at `k + 1`. -/
-- The object formula must compute to give tower arrows their concrete quotient-ring types.
@[expose]
def quotientDiagram : ℕᵒᵖ ⥤ RingCat where
  obj k := RingCat.of (A ⧸ F.ideal (k.unop + 1))
  map f := RingCat.ofHom (Ideal.Quotient.factor
    (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1)))
  map_id _ := RingCat.hom_ext Ideal.Quotient.factor_eq
  map_comp f g := RingCat.hom_ext (Ideal.Quotient.factor_comp
    (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1))
    (F.antitone (Nat.add_le_add_right (leOfHom g.unop) 1))).symm

/-- The order-`k` object is the quotient by the ideal at `k + 1`. -/
@[simp]
theorem quotientDiagram_obj (k : ℕᵒᵖ) :
    F.quotientDiagram.obj k = RingCat.of (A ⧸ F.ideal (k.unop + 1)) := (rfl)

/-- Tower arrows are the canonical quotient ring maps. -/
@[simp]
theorem quotientDiagram_map_hom {k l : ℕᵒᵖ} (f : k ⟶ l) :
    (F.quotientDiagram.map f).hom = Ideal.Quotient.factor
      (F.antitone (Nat.add_le_add_right (leOfHom f.unop) 1)) := (rfl)

/-- The completion is the subring of compatible families in the quotient tower. -/
def completion : Subring (∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) :=
  RingCat.sectionsSubring F.quotientDiagram

/-- Compatibility in the completion is exactly compatibility under all quotient maps. -/
@[simp]
theorem mem_completion_iff (x : ∀ k : ℕᵒᵖ, A ⧸ F.ideal (k.unop + 1)) :
    x ∈ F.completion ↔ ∀ {k l : ℕ} (h : k ≤ l),
      Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (x (op l)) =
        x (op k) := by
  constructor
  · intro hx k l h
    exact hx (homOfLE h).op
  · intro hx k l f
    exact hx (leOfHom f.unop)

/-- Projection of the completion to its order-`k` quotient. -/
def projection (k : ℕ) : F.completion →+* A ⧸ F.ideal (k + 1) :=
  (Pi.evalRingHom _ (op k)).comp F.completion.subtype

/-- Projections evaluate compatible families. -/
theorem projection_apply (k : ℕ) (x : F.completion) :
    F.projection k x = x.val (op k) := (rfl)

/-- Projections commute with the transition maps of the quotient tower. -/
@[simp]
theorem factor_projection {k l : ℕ} (h : k ≤ l) (x : F.completion) :
    Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1)) (F.projection l x) =
      F.projection k x :=
  (F.mem_completion_iff x.val).mp x.property h

/-- Elements of the completion are determined by all their finite-order projections. -/
@[ext]
theorem completion_ext {x y : F.completion}
    (h : ∀ k, F.projection k x = F.projection k y) : x = y := by
  apply Subtype.ext
  funext k
  exact h k.unop

variable {B : Type*} [Semiring B]

/-- A compatible family of ring maps into the quotients lifts to the completion. -/
def lift (f : ∀ k, B →+* A ⧸ F.ideal (k + 1))
    (hf : ∀ {k l} (h : k ≤ l),
      (Ideal.Quotient.factor (F.antitone (Nat.add_le_add_right h 1))).comp (f l) = f k) :
    B →+* F.completion :=
  (RingHom.pi (fun k : ℕᵒᵖ => f k.unop)).codRestrict F.completion fun x =>
    (F.mem_completion_iff _).mpr fun h => RingHom.congr_fun (hf h) x

/-- The lift has the specified finite-order components. -/
@[simp]
theorem projection_lift (f : ∀ k, B →+* A ⧸ F.ideal (k + 1)) (hf) (k : ℕ) (x : B) :
    F.projection k (F.lift f hf x) = f k x := (rfl)

/-- Ring maps to the completion are determined by their finite-order components. -/
theorem hom_ext {f g : B →+* F.completion}
    (h : ∀ k, (F.projection k).comp f = (F.projection k).comp g) : f = g := by
  apply RingHom.ext
  intro x
  exact F.completion_ext fun k => RingHom.congr_fun (h k) x

/-- The canonical ring homomorphism sends an element to its classes at all orders. -/
def toCompletion : A →+* F.completion :=
  F.lift (fun k => Ideal.Quotient.mk (F.ideal (k + 1)))
    (fun _ => Ideal.Quotient.factor_comp_mk _)

/-- Finite-order projection of the canonical map is the quotient map. -/
@[simp]
theorem projection_toCompletion (k : ℕ) (x : A) :
    F.projection k (F.toCompletion x) = Ideal.Quotient.mk (F.ideal (k + 1)) x := (rfl)

/-- The kernel of the canonical map is the intersection of the filtration. -/
theorem ker_toCompletion : RingHom.ker F.toCompletion = ⨅ k, F.ideal k := by
  ext x
  simp only [RingHom.mem_ker, Submodule.mem_iInf]
  constructor
  · intro hx k
    cases k with
    | zero => simp
    | succ k =>
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa using congrArg (F.projection k) hx
  · intro hx
    apply F.completion_ext
    intro k
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (hx (k + 1))

/-- The completion cone has the finite-order projections as its legs. -/
def completionCone : Cone F.quotientDiagram where
  pt := RingCat.of F.completion
  π :=
    { app := fun k => RingCat.ofHom (F.projection k.unop)
      naturality := by
        intro k l f
        apply RingCat.hom_ext
        ext x
        exact (F.factor_projection (leOfHom f.unop) x).symm }

/-- The point of the completion cone is the compatible-family completion. -/
@[simp]
theorem completionCone_pt : F.completionCone.pt = RingCat.of F.completion := (rfl)

/-- Under the point and quotient-object identifications, the cone legs are the projections. -/
@[simp]
theorem completionCone_π_app (k : ℕᵒᵖ) :
    F.completionCone.π.app k =
      eqToHom F.completionCone_pt ≫ RingCat.ofHom (F.projection k.unop) ≫
        eqToHom (F.quotientDiagram_obj k).symm := (rfl)

/-- The compatible-family completion satisfies the categorical inverse-limit property. -/
def completionConeIsLimit : IsLimit F.completionCone where
  lift s := RingCat.ofHom (F.lift (fun k => (s.π.app (op k)).hom) (by
    intro k l h
    exact congrArg RingCat.Hom.hom (s.w (homOfLE h).op)))
  fac _ _ := rfl
  uniq s m hm := by
    apply RingCat.hom_ext
    apply F.hom_ext
    intro k
    exact congrArg RingCat.Hom.hom (hm (op k))

/-- The ideal of completion elements vanishing below order `n`; order zero is unrestricted. -/
def completionIdeal : ℕ → Ideal F.completion
  | 0 => ⊤
  | k + 1 => RingHom.ker (F.projection k)

/-- The zero-order completion ideal is the whole completion. -/
@[simp]
theorem completionIdeal_zero : F.completionIdeal 0 = ⊤ := (rfl)

/-- Positive-order completion ideals are kernels of finite-order projections. -/
@[simp]
theorem completionIdeal_succ (k : ℕ) :
    F.completionIdeal (k + 1) = RingHom.ker (F.projection k) := (rfl)

/-- All induced completion ideals are two-sided. -/
instance completionIdeal_isTwoSided (k : ℕ) : (F.completionIdeal k).IsTwoSided := by
  cases k <;> simp only [completionIdeal_zero, completionIdeal_succ] <;> infer_instance

/-- Vanishing to a higher order implies vanishing to every lower order. -/
theorem completionIdeal_antitone : Antitone F.completionIdeal := by
  intro k l h x hx
  cases k with
  | zero => simp
  | succ k =>
    cases l with
    | zero => omega
    | succ l =>
      have hx0 : F.projection l x = 0 := RingHom.mem_ker.mp hx
      have hx' := congrArg (Ideal.Quotient.factor
        (F.antitone (Nat.add_le_add_right (Nat.le_of_succ_le_succ h) 1))) hx0
      rw [F.factor_projection (Nat.le_of_succ_le_succ h), map_zero] at hx'
      exact RingHom.mem_ker.mpr hx'

/-- Multiplication in the completion adds vanishing orders. -/
theorem mul_mem_completionIdeal {a b : ℕ} {x y : F.completion}
    (hx : x ∈ F.completionIdeal a) (hy : y ∈ F.completionIdeal b) :
    x * y ∈ F.completionIdeal (a + b) := by
  cases a with
  | zero => simpa using (F.completionIdeal b).mul_mem_left x hy
  | succ a =>
    cases b with
    | zero => simpa using (F.completionIdeal (a + 1)).mul_mem_right y hx
    | succ b =>
      have hab : a + 1 + (b + 1) = (a + b + 1) + 1 := by omega
      rw [hab, completionIdeal_succ, RingHom.mem_ker, map_mul]
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (F.projection (a + b + 1) x)
      obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (F.projection (a + b + 1) y)
      have hxr : r ∈ F.ideal (a + 1) := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have h := congrArg (Ideal.Quotient.factor
          (F.antitone (by omega : a + 1 ≤ (a + b + 1) + 1))) hr
        rw [Ideal.Quotient.factor_mk,
          F.factor_projection (by omega : a ≤ a + b + 1)] at h
        exact h.trans (RingHom.mem_ker.mp hx)
      have hys : s ∈ F.ideal (b + 1) := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have h := congrArg (Ideal.Quotient.factor
          (F.antitone (by omega : b + 1 ≤ (a + b + 1) + 1))) hs
        rw [Ideal.Quotient.factor_mk,
          F.factor_projection (by omega : b ≤ a + b + 1)] at h
        exact h.trans (RingHom.mem_ker.mp hy)
      rw [← hr, ← hs, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using F.mul_mem hxr hys

/-- The induced decreasing multiplicative filtration on the completion. -/
def completionFiltration : TauCeti.AlgFiltration F.completion where
  ideal := F.completionIdeal
  isTwoSided := F.completionIdeal_isTwoSided
  antitone := F.completionIdeal_antitone
  ideal_zero := F.completionIdeal_zero
  mul_mem := fun {_ _ _ _} hx hy => F.mul_mem_completionIdeal hx hy

/-- The terms of the induced filtration are the vanishing-order ideals. -/
@[simp]
theorem completionFiltration_ideal (k : ℕ) :
    F.completionFiltration.ideal k = F.completionIdeal k := (rfl)

/-- The canonical map preserves and reflects each filtration order. -/
@[simp]
theorem toCompletion_mem_completionIdeal_iff (k : ℕ) (x : A) :
    F.toCompletion x ∈ F.completionIdeal k ↔ x ∈ F.ideal k := by
  cases k with
  | zero => simp
  | succ k => simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- The induced filtration on the completion is separated. -/
@[simp]
theorem iInf_completionIdeal_eq_bot : ⨅ k, F.completionIdeal k = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply F.completion_ext
  intro k
  simpa only [map_zero] using
    RingHom.mem_ker.mp ((Submodule.mem_iInf F.completionIdeal).mp hx (k + 1))

/-- The order-`k` projection of an element of the first completion ideal has
vanishing `(k + 1)`-st power. -/
theorem projection_pow_eq_zero {x : F.completion}
    (hx : x ∈ F.completionIdeal 1) (k : ℕ) :
    F.projection k x ^ (k + 1) = 0 := by
  have hx' : x ∈ F.completionFiltration.orderDual (OrderDual.toDual 1) := by
    simpa only [orderDual_apply, OrderDual.ofDual_toDual, completionFiltration_ideal] using hx
  have hp := SetLike.pow_mem_graded (k + 1) hx'
  simpa [orderDual_apply, nsmul_eq_mul, completionIdeal_succ, RingHom.mem_ker] using hp

/-- Elements of the first completion ideal are nilpotent at every finite order. -/
theorem isNilpotent_projection {x : F.completion}
    (hx : x ∈ F.completionIdeal 1) (k : ℕ) : IsNilpotent (F.projection k x) :=
  ⟨k + 1, F.projection_pow_eq_zero hx k⟩

end TauCeti.AlgFiltration
