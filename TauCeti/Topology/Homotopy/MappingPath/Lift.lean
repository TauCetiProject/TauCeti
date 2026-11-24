/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Homotopic.Homotopy
public import TauCeti.Topology.Homotopy.MappingPath.Fiber

/-!
# Lifts through a mapping-path fibre

Let `f : B → K` be a map, `k` a point of `K` and `c : X → B` a map. A lift of `c` through the
source projection `MappingPathFiber f k → B` (`TauCeti.MappingPathFiber.Lift f k c`) assigns to
each point `x` a path from `f (c x)` to `k`, continuously in `x`. These are exactly the
nullhomotopies of `f ∘ c`, the homotopies from `f ∘ c` to the constant map at `k`
(`TauCeti.MappingPathFiber.liftEquivHomotopy`), and in particular `c` lifts exactly when `f ∘ c`
is homotopic to the constant map at `k` (`TauCeti.MappingPathFiber.nonempty_lift_iff`).

Two lifts are homotopic over `c` (`TauCeti.MappingPathFiber.Lift.Homotopic`) when they are
homotopic through lifts of `c`, that is, when the corresponding nullhomotopies are homotopic
relative to their ends. A family of loops `α : X → Ω K k` can be appended to a lift, appending
the loop `α x` to the path of each point (`TauCeti.MappingPathFiber.Lift.appendLoops`), and two
lifts `l₀ l₁` have the difference `x ↦ (l₀.path x).symm.trans (l₁.path x)`
(`TauCeti.MappingPathFiber.Lift.difference`). Up to homotopy these operations are inverse: for
every lift `l₀`, taking differences from `l₀` identifies the homotopy classes of lifts of `c`
with the homotopy classes of maps `X → Ω K k` (`TauCeti.MappingPathFiber.Lift.classEquiv`), and
the inverse appends a family of loops to `l₀`. Up to homotopy, appending loops is unital and
associative, and differences vanish on the diagonal and satisfy the cocycle law
(`TauCeti.MappingPathFiber.Lift.homotopic_difference_pathTrans_difference`). Differences are
natural under restriction along maps `X' → X` (`TauCeti.MappingPathFiber.Lift.difference_comp`).

This is the classification of lifts through a homotopy fibre. When `K` is an Eilenberg–MacLane
space `K(A, n)`, maps from a CW complex `X` to its loop space `K(A, n - 1)` represent
`Hⁿ⁻¹(X; A)`, so the homotopy classes of lifts, when there are any, correspond to the elements
of that cohomology group once a reference lift is chosen.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and III.
* C. Redden, *String structures and canonical 3-forms*, Pacific J. Math. 249 (2011),
  Proposition 2.2.
-/

public section

open unitInterval ContinuousMap Topology.Homotopy

namespace TauCeti.MappingPathFiber

variable {X B K : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace K]
  (f : C(B, K)) (k : K) (c : C(X, B))

/-- The lifts of `c : X → B` through the source projection `MappingPathFiber f k → B`. -/
abbrev Lift : Type _ :=
  {l : C(X, MappingPathFiber f k) // (proj f k).comp l = c}

variable {f k c}

namespace Lift

/-- The source point of a lift of `c` at `x` is `c x`. -/
@[simp]
theorem apply_val_fst (l : Lift f k c) (x : X) : (l.val x).val.1 = c x := by
  simpa using DFunLike.congr_fun l.property x

/-- The path from `f (c x)` to `k` that a lift of `c` assigns to the point `x`. -/
def path (l : Lift f k c) (x : X) : Path (f (c x)) k where
  toFun t := (l.val x).val.2 t
  source' := by simp [(l.val x).property.1]
  target' := (l.val x).property.2

theorem path_apply (l : Lift f k c) (x : X) (t : I) : l.path x t = (l.val x).val.2 t :=
  (rfl)

/-- Lifts of `c` are determined by their paths. -/
theorem ext {l₀ l₁ : Lift f k c} (h : ∀ x, l₀.path x = l₁.path x) : l₀ = l₁ := by
  refine Subtype.ext (ContinuousMap.ext fun x ↦ Subtype.ext (Prod.ext (by simp) ?_))
  ext t
  exact DFunLike.congr_fun (h x) t

end Lift

variable (f k c) in
/-- Lifts of `c` through the mapping-path fibre are the nullhomotopies of `f ∘ c`: a lift `l`
corresponds to the homotopy `(t, x) ↦ l.path x t` from `f ∘ c` to the constant map at `k`. -/
def liftEquivHomotopy : Lift f k c ≃ Homotopy (f.comp c) (const X k) where
  toFun l :=
    { toFun p := l.path p.2 p.1
      continuous_toFun := continuous_eval.comp
        ((continuous_subtypeVal.snd.comp (l.val.continuous.comp continuous_snd)).prodMk
          continuous_fst)
      map_zero_left x := (l.path x).source
      map_one_left x := (l.path x).target }
  invFun F :=
    ⟨{ toFun x := ⟨(c x, (F.toContinuousMap.comp .prodSwap).curry x), by simp, by simp⟩
       continuous_toFun := (c.continuous.prodMk
         (F.toContinuousMap.comp .prodSwap).curry.continuous).subtype_mk _ },
      ContinuousMap.ext fun x ↦ by simp⟩
  left_inv l := Lift.ext fun x ↦ Path.ext (rfl)
  right_inv _ := (rfl)

@[simp]
theorem liftEquivHomotopy_apply (l : Lift f k c) (t : I) (x : X) :
    liftEquivHomotopy f k c l (t, x) = l.path x t :=
  (rfl)

@[simp]
theorem evalAt_liftEquivHomotopy (l : Lift f k c) (x : X) :
    (liftEquivHomotopy f k c l).evalAt x = l.path x :=
  (rfl)

@[simp]
theorem path_liftEquivHomotopy_symm (F : Homotopy (f.comp c) (const X k)) (x : X) :
    ((liftEquivHomotopy f k c).symm F).path x = F.evalAt x :=
  (rfl)

/-- A map `c` lifts through the mapping-path fibre exactly when `f ∘ c` is homotopic to the
constant map at `k`. -/
theorem nonempty_lift_iff : Nonempty (Lift f k c) ↔ (f.comp c).Homotopic (const X k) :=
  (liftEquivHomotopy f k c).nonempty_congr

namespace Lift

/-- Two lifts of `c` are homotopic over `c` when they are homotopic through lifts of `c`. -/
def Homotopic (l₀ l₁ : Lift f k c) : Prop :=
  l₀.val.HomotopicWith l₁.val fun l ↦ (proj f k).comp l = c

theorem homotopic_def {l₀ l₁ : Lift f k c} :
    l₀.Homotopic l₁ ↔ l₀.val.HomotopicWith l₁.val fun l ↦ (proj f k).comp l = c :=
  Iff.rfl

/-- Lifts of `c` are homotopic over `c` exactly when the corresponding nullhomotopies of `f ∘ c`
are homotopic relative to their ends. A homotopy over `c` is a lift of `c ∘ snd` on `I × X`,
that is, a nullhomotopy of `f ∘ c ∘ snd`. -/
theorem homotopic_iff {l₀ l₁ : Lift f k c} :
    l₀.Homotopic l₁ ↔ (liftEquivHomotopy f k c l₀).Homotopic (liftEquivHomotopy f k c l₁) := by
  rw [Homotopy.homotopic_iff_exists]
  constructor
  · rintro ⟨L⟩
    let L' : Lift f k (c.comp .snd) :=
      ⟨L.toContinuousMap, ContinuousMap.ext fun p ↦ by
        simpa using DFunLike.congr_fun (L.prop p.1) p.2⟩
    exact ⟨liftEquivHomotopy f k _ L', fun t x ↦ congrArg (fun p ↦ p.val.2 t) (L.apply_zero x),
      fun t x ↦ congrArg (fun p ↦ p.val.2 t) (L.apply_one x)⟩
  · rintro ⟨H, h₀, h₁⟩
    let L' := (liftEquivHomotopy f k (c.comp .snd)).symm H
    exact ⟨{ toContinuousMap := L'.val
             map_zero_left x := Subtype.ext (Prod.ext (by simp [L']) (ContinuousMap.ext (h₀ · x)))
             map_one_left x := Subtype.ext (Prod.ext (by simp [L']) (ContinuousMap.ext (h₁ · x)))
             prop' s := ContinuousMap.ext fun x ↦ by simp [L'] }⟩

@[refl]
theorem Homotopic.refl (l : Lift f k c) : l.Homotopic l :=
  homotopic_iff.2 (.refl _)

@[symm]
theorem Homotopic.symm ⦃l₀ l₁ : Lift f k c⦄ (h : l₀.Homotopic l₁) : l₁.Homotopic l₀ :=
  homotopic_iff.2 (homotopic_iff.1 h).symm

@[trans]
theorem Homotopic.trans ⦃l₀ l₁ l₂ : Lift f k c⦄ (h₀ : l₀.Homotopic l₁) (h₁ : l₁.Homotopic l₂) :
    l₀.Homotopic l₂ :=
  homotopic_iff.2 ((homotopic_iff.1 h₀).trans (homotopic_iff.1 h₁))

theorem Homotopic.equivalence : Equivalence (Homotopic : Lift f k c → Lift f k c → Prop) :=
  ⟨Homotopic.refl, (Homotopic.symm ·), (Homotopic.trans · ·)⟩

variable (f k c) in
/-- The setoid of lifts of `c` up to homotopy over `c`. -/
def setoid : Setoid (Lift f k c) :=
  ⟨Homotopic, Homotopic.equivalence⟩

@[simp]
theorem setoid_apply (l₀ l₁ : Lift f k c) : setoid f k c l₀ l₁ ↔ l₀.Homotopic l₁ :=
  Iff.rfl

theorem quotientMk_eq_iff {l₀ l₁ : Lift f k c} :
    Quotient.mk (setoid f k c) l₀ = Quotient.mk _ l₁ ↔ l₀.Homotopic l₁ :=
  Quotient.eq

/-- Append to the path of each point `x` of a lift of `c` the loop `α x` at `k`. -/
noncomputable def appendLoops (l : Lift f k c) (α : C(X, Ω K k)) : Lift f k c :=
  (liftEquivHomotopy f k c).symm
    ((liftEquivHomotopy f k c l).trans (Homotopy.evalAtEquiv.symm α))

@[simp]
theorem liftEquivHomotopy_appendLoops (l : Lift f k c) (α : C(X, Ω K k)) :
    liftEquivHomotopy f k c (l.appendLoops α) =
      (liftEquivHomotopy f k c l).trans (Homotopy.evalAtEquiv.symm α) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem path_appendLoops (l : Lift f k c) (α : C(X, Ω K k)) (x : X) :
    (l.appendLoops α).path x = (l.path x).trans (α x) := by
  simp [appendLoops]

/-- The difference of two lifts of `c`: at each point `x`, the loop at `k` that reverses the path
of `l₀` and then follows the path of `l₁`. -/
noncomputable def difference (l₀ l₁ : Lift f k c) : C(X, Ω K k) :=
  Homotopy.evalAtEquiv ((liftEquivHomotopy f k c l₀).symm.trans (liftEquivHomotopy f k c l₁))

theorem difference_def (l₀ l₁ : Lift f k c) :
    difference l₀ l₁ =
      Homotopy.evalAtEquiv ((liftEquivHomotopy f k c l₀).symm.trans (liftEquivHomotopy f k c l₁)) :=
  (rfl)

@[simp]
theorem evalAtEquiv_symm_difference (l₀ l₁ : Lift f k c) :
    Homotopy.evalAtEquiv.symm (difference l₀ l₁) =
      (liftEquivHomotopy f k c l₀).symm.trans (liftEquivHomotopy f k c l₁) :=
  Equiv.symm_apply_apply _ _

@[simp]
theorem difference_apply (l₀ l₁ : Lift f k c) (x : X) :
    difference l₀ l₁ x = (l₀.path x).symm.trans (l₁.path x) := by
  simp [difference]

/-- Appending the difference from `l₀` to `l₁` to `l₀` gives a lift homotopic to `l₁` over `c`.
So every lift is homotopic over `c` to `l₀` with some family of loops appended. -/
theorem homotopic_appendLoops_difference (l₀ l₁ : Lift f k c) :
    (l₀.appendLoops (difference l₀ l₁)).Homotopic l₁ :=
  homotopic_iff.2 <| by simpa using Homotopy.Homotopic.trans_symm_trans _ _

/-- The difference from `l₀` to `l₀` with a family `α` of loops appended is homotopic to `α`. -/
theorem homotopic_difference_appendLoops (l₀ : Lift f k c) (α : C(X, Ω K k)) :
    (difference l₀ (l₀.appendLoops α)).Homotopic α := by
  simpa [difference] using Homotopy.homotopic_iff_evalAtEquiv.1
    (Homotopy.Homotopic.symm_trans_trans (liftEquivHomotopy f k c l₀)
      (Homotopy.evalAtEquiv.symm α))

/-- Appending homotopic families of loops to lifts homotopic over `c` gives lifts homotopic
over `c`. -/
theorem Homotopic.appendLoops {l₀ l₁ : Lift f k c} {α β : C(X, Ω K k)} (hl : l₀.Homotopic l₁)
    (hα : α.Homotopic β) : (l₀.appendLoops α).Homotopic (l₁.appendLoops β) :=
  homotopic_iff.2 <| by
    simpa using Homotopy.Homotopic.hcomp (homotopic_iff.1 hl)
      (Homotopy.homotopic_iff_evalAtEquiv.2 (by simpa using hα))

/-- The differences between lifts homotopic over `c` are homotopic. -/
theorem Homotopic.difference {l₀ l₀' l₁ l₁' : Lift f k c} (h₀ : l₀.Homotopic l₀')
    (h₁ : l₁.Homotopic l₁') : (Lift.difference l₀ l₁).Homotopic (Lift.difference l₀' l₁') :=
  Homotopy.homotopic_iff_evalAtEquiv.1
    (Homotopy.Homotopic.hcomp (homotopic_iff.1 h₀).symm₂ (homotopic_iff.1 h₁))

/-- Appending the constant family of constant loops gives a lift homotopic to the original one
over `c`. -/
theorem homotopic_appendLoops_const_refl (l : Lift f k c) :
    (l.appendLoops (const X (Path.refl k))).Homotopic l :=
  homotopic_iff.2 <| by
    rw [liftEquivHomotopy_appendLoops, ← Homotopy.evalAtEquiv_refl, Equiv.symm_apply_apply]
    exact Homotopy.Homotopic.trans_refl _

/-- Appending two families of loops in turn is homotopic over `c` to appending their pointwise
concatenation. -/
theorem homotopic_appendLoops_appendLoops (l : Lift f k c) (α β : C(X, Ω K k)) :
    ((l.appendLoops α).appendLoops β).Homotopic (l.appendLoops (α.pathTrans β)) :=
  homotopic_iff.2 <| by simpa using Homotopy.Homotopic.trans_assoc _ _ _

/-- The difference from a lift to itself is homotopic to the constant family of constant
loops. -/
theorem homotopic_difference_self (l : Lift f k c) :
    (difference l l).Homotopic (const X (Path.refl k)) := by
  rw [difference_def, ← Homotopy.evalAtEquiv_refl]
  exact Homotopy.homotopic_iff_evalAtEquiv.1 (Homotopy.Homotopic.symm_trans _)

/-- The cocycle law: the pointwise concatenation of the difference from `l₀` to `l₁` and the
difference from `l₁` to `l₂` is homotopic to the difference from `l₀` to `l₂`. -/
theorem homotopic_difference_pathTrans_difference (l₀ l₁ l₂ : Lift f k c) :
    ((difference l₀ l₁).pathTrans (difference l₁ l₂)).Homotopic (difference l₀ l₂) := by
  simp only [difference_def, ← Homotopy.evalAtEquiv_trans]
  exact Homotopy.homotopic_iff_evalAtEquiv.1 (Homotopy.Homotopic.symm_trans_trans_symm_trans _ _ _)

/-- Taking differences from a lift `l₀` identifies the homotopy classes of lifts of `c` over `c`
with the homotopy classes of maps `X → Ω K k`; the inverse appends a family of loops to `l₀`. -/
noncomputable def classEquiv (l₀ : Lift f k c) :
    Quotient (setoid f k c) ≃ Quotient (⟨ContinuousMap.Homotopic,
      ContinuousMap.Homotopic.equivalence⟩ : Setoid C(X, Ω K k)) where
  toFun := Quotient.map (difference l₀) fun _ _ ↦ (Homotopic.refl l₀).difference
  invFun := Quotient.map l₀.appendLoops fun _ _ ↦ (Homotopic.refl l₀).appendLoops
  left_inv q := by
    induction q using Quotient.ind with | _ l₁
    exact Quotient.sound (homotopic_appendLoops_difference l₀ l₁)
  right_inv q := by
    induction q using Quotient.ind with | _ α
    exact Quotient.sound (homotopic_difference_appendLoops l₀ α)

@[simp]
theorem classEquiv_mk (l₀ l₁ : Lift f k c) :
    classEquiv l₀ (Quotient.mk _ l₁) = Quotient.mk _ (difference l₀ l₁) :=
  (rfl)

@[simp]
theorem classEquiv_symm_mk (l₀ : Lift f k c) (α : C(X, Ω K k)) :
    (classEquiv l₀).symm (Quotient.mk _ α) = Quotient.mk _ (l₀.appendLoops α) :=
  (rfl)

/-- Appending two families of loops to the same lift gives lifts homotopic over `c` exactly when
the families are homotopic. -/
@[simp]
theorem appendLoops_homotopic_appendLoops_iff (l : Lift f k c) {α β : C(X, Ω K k)} :
    (l.appendLoops α).Homotopic (l.appendLoops β) ↔ α.Homotopic β := by
  refine ⟨fun h ↦ ?_, (Homotopic.refl l).appendLoops⟩
  exact ((homotopic_difference_appendLoops l α).symm.trans
    ((Homotopic.refl l).difference h)).trans
    (homotopic_difference_appendLoops l β)

/-! ### Naturality -/

variable {X' : Type*} [TopologicalSpace X']

/-- The restriction of a lift of `c` along a map `g : X' → X`, a lift of `c ∘ g`. -/
def comp (l : Lift f k c) (g : C(X', X)) : Lift f k (c.comp g) :=
  ⟨l.val.comp g, by rw [← ContinuousMap.comp_assoc, l.property]⟩

@[simp]
theorem val_comp (l : Lift f k c) (g : C(X', X)) : (l.comp g).val = l.val.comp g :=
  (rfl)

@[simp]
theorem path_comp (l : Lift f k c) (g : C(X', X)) (x : X') :
    (l.comp g).path x = l.path (g x) :=
  (rfl)

/-- Restricting a lift along `g` restricts the corresponding nullhomotopy along `g`. -/
@[simp]
theorem liftEquivHomotopy_comp (l : Lift f k c) (g : C(X', X)) :
    liftEquivHomotopy f k (c.comp g) (l.comp g) = (liftEquivHomotopy f k c l).compContinuousMap g :=
  (rfl)

/-- Restricting lifts along `g` preserves homotopy over `c`. -/
theorem Homotopic.comp {l₀ l₁ : Lift f k c} (h : l₀.Homotopic l₁) (g : C(X', X)) :
    (l₀.comp g).Homotopic (l₁.comp g) := by
  obtain ⟨L⟩ := h
  refine ⟨{ toHomotopy := L.toHomotopy.compContinuousMap g, prop' := fun s ↦ ?_ }⟩
  ext x
  simpa using DFunLike.congr_fun (L.prop s) (g x)

/-- Appending loops commutes with restriction along `g`. -/
@[simp]
theorem appendLoops_comp (l : Lift f k c) (α : C(X, Ω K k)) (g : C(X', X)) :
    (l.appendLoops α).comp g = (l.comp g).appendLoops (α.comp g) :=
  ext fun x ↦ by simp

/-- Differences commute with restriction along `g`. -/
@[simp]
theorem difference_comp (l₀ l₁ : Lift f k c) (g : C(X', X)) :
    difference (l₀.comp g) (l₁.comp g) = (difference l₀ l₁).comp g := by
  ext x : 1
  simp

end Lift

end TauCeti.MappingPathFiber
