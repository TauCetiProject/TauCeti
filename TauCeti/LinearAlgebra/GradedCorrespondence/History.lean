/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Path
public import TauCeti.LinearAlgebra.Graded.History.Basic

/-!
# Component expansions of zero-extended transfers

The *total transfer* of a graded correspondence is its total left lift followed by
the right leg. On an admissible homogeneous piece it is the lift across the span,
whose homogeneous components are the transfers; it vanishes on inadmissible pieces.
It is linear on mixed inputs, so graded correspondences on the arrows of a quiver,
between the decomposed modules at their endpoints, give linear arrow maps between
differently graded chamber modules.

The path histories of total transfers are the finite component expansion of
transfer compositions. Each step selects one transfer component of the whole previous
decoration, and the step is zero when that decoration has inadmissible degree
(`homogeneousHistory_totalTransfer_cons_apply`). For a fixed input the nonzero histories
are finite and sum to the composite of total transfers, by the general
`Quiver.Path.sum_homogeneousHistory` applied to the arrow maps `(C e).totalTransfer`.

The single-step formula is `decompose_right_liftLeftTotal_of_mem`. Selecting the
same admissible degree at every vertex, the history of a path on the incoming
homogeneous piece is the selected-transfer functor `GradedCorrespondence.transferFunctor`
(`transferFunctor_map_hom_eq_homogeneousHistory`).

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/History.lean` and
`Mei/LinearAlgebra/GradedCorrespondence/History/Regrouping.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public noncomputable section

namespace TauCeti.GradedCorrespondence

variable {R : Type*} [Semiring R] {Q : Type*} [Quiver Q]
  {M : Q → Type*} [∀ q, AddCommMonoid (M q)] [∀ q, Module R (M q)]
  {ι : Q → Type*} [∀ q, DecidableEq (ι q)] (ℳ : ∀ q, ι q → Submodule R (M q))
  [∀ q, DirectSum.Decomposition (ℳ q)]
  {B : ∀ {b c : Q}, (b ⟶ c) → Type*} [∀ (b c : Q) (e : b ⟶ c), AddCommMonoid (B e)]
  [∀ (b c : Q) (e : b ⟶ c), Module R (B e)]
  {I : ∀ {b c : Q}, (b ⟶ c) → Set (ι b)} {J : ∀ {b c : Q}, (b ⟶ c) → Set (ι c)}
  (C : ∀ {b c : Q} (e : b ⟶ c), GradedCorrespondence (B := B e) (ℳ b) (ℳ c) (I e) (J e))

/-- Each step of a transfer history selects one transfer component of the whole
previous decoration. A decoration of inadmissible degree contributes zero. -/
theorem homogeneousHistory_totalTransfer_cons_apply {a b c : Q} (p : Quiver.Path a b)
    (e : b ⟶ c) (d : p.Degrees ι) (j : ι c) (x : M a) {i : ι b} [Decidable (i ∈ I e)]
    (hx : p.homogeneousHistory (fun e => (C e).totalTransfer) ℳ d x ∈ ℳ b i) :
    (p.cons e).homogeneousHistory (fun e => (C e).totalTransfer) ℳ
        ((d, j) : (p.cons e).Degrees ι) x =
      if hi : i ∈ I e then ((C e).transfer ⟨i, hi⟩ j ⟨_, hx⟩ : M c) else 0 := by
  rw [Quiver.Path.homogeneousHistory_cons_apply, totalTransfer_apply,
    (C e).decompose_right_liftLeftTotal_of_mem hx]
  split_ifs <;> rfl

/-- A transfer history whose decoration before the final crossing has inadmissible
degree vanishes. -/
theorem homogeneousHistory_totalTransfer_cons_eq_zero_of_notMem {a b c : Q}
    (p : Quiver.Path a b) (e : b ⟶ c) (d : p.Degrees ι) (j : ι c) (x : M a) {i : ι b}
    (hi : i ∉ I e)
    (hx : p.homogeneousHistory (fun e => (C e).totalTransfer) ℳ d x ∈ ℳ b i) :
    (p.cons e).homogeneousHistory (fun e => (C e).totalTransfer) ℳ
        ((d, j) : (p.cons e).Degrees ι) x = 0 := by
  classical
  rw [homogeneousHistory_totalTransfer_cons_apply ℳ C p e d j x hx, dite_eq_right hi]

local notation "T" => fun e => totalTransfer (C e)

/-- Selected homogeneous path propagation is precisely the corresponding
zero-extended transfer history on its incoming homogeneous piece. This compares
the two existing constructions without an assumption that any decoration survives. -/
theorem transferFunctor_map_hom_eq_homogeneousHistory
    (s : ∀ q, ι q) (hs : ∀ {b c : Q} (e : b ⟶ c), s b ∈ I e)
    {a b : Q} (p : Quiver.Path a b) :
    (ℳ b (s b)).subtype.comp (((transferFunctor ℳ C s hs).map p).hom) =
      (p.homogeneousHistory T ℳ (p.degreesOfVertices s)).comp (ℳ a (s a)).subtype := by
  classical
  -- Expand the free extension to use Mathlib's path recursion. The component
  -- transfers are evaluated only through their public single-step formula.
  unfold transferFunctor
  induction p with
  | nil =>
    -- The objects of `Paths Q` use a type synonym for the original vertices.
    erw [CategoryTheory.Paths.lift_nil, SemimoduleCat.hom_id,
      LinearMap.comp_id, Quiver.Path.homogeneousHistory_nil, LinearMap.id_comp]
  | @cons b c p e ih =>
    refine LinearMap.ext fun (x : ℳ a (s a)) => ?_
    have hx := LinearMap.congr_fun ih x
    erw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.subtype_apply] at hx
    have hmem : p.homogeneousHistory T ℳ (p.degreesOfVertices s) x ∈ ℳ b (s b) :=
      hx ▸ Subtype.property _
    calc
      _ = ((C e).transfer ⟨s b, hs e⟩ (s c)
          (((transferFunctor ℳ C s hs).map p).hom x) : M c) := by
        erw [CategoryTheory.Paths.lift_cons, transferPrefunctor_map,
          SemimoduleCat.hom_comp, SemimoduleCat.hom_ofHom,
          LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      _ = ((C e).transfer ⟨s b, hs e⟩ (s c) ⟨_, hmem⟩ : M c) := by
        exact congrArg (fun y : ℳ b (s b) =>
          ((C e).transfer ⟨s b, hs e⟩ (s c) y : M c)) (Subtype.ext hx)
      _ = (p.cons e).homogeneousHistory T ℳ
          ((p.cons e).degreesOfVertices s) (x : M a) := by
        simpa only [Quiver.Path.degreesOfVertices_cons, dite_eq_left (hs e),
          LinearMap.comp_apply, Submodule.subtype_apply] using
          (homogeneousHistory_totalTransfer_cons_apply ℳ C p e
            (p.degreesOfVertices s) (s c) (x : M a) hmem).symm
      _ = _ := (LinearMap.comp_apply
        ((p.cons e).homogeneousHistory T ℳ ((p.cons e).degreesOfVertices s))
        (ℳ a (s a)).subtype x).symm

end TauCeti.GradedCorrespondence
