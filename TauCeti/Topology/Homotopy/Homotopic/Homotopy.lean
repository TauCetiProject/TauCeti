/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Homotopies between homotopies

Two homotopies `F G : ContinuousMap.Homotopy f₀ f₁` are *homotopic*
(`ContinuousMap.Homotopy.Homotopic`) when they are homotopic relative to their ends
`{0, 1} × X`. At each point `x` this is a homotopy of the paths `F.evalAt x` and `G.evalAt x`
traced by `x`, depending continuously on `x`. Up to this relation the homotopies between maps
`X → Y` behave like the paths of a groupoid, with a parameter in `X`: concatenation and reversal
respect the relation (`Homotopic.hcomp`, `Homotopic.symm₂`), concatenation is associative and
unital, and reversal is inverse to concatenation. The proofs follow the reparametrization
arguments for paths in `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic`, carried out
uniformly in the parameter.

Consequently, for a fixed homotopy `F₀` from `f₀` to `f₁`, appending self-homotopies of `f₁`
to `F₀` and taking differences `F₀.symm.trans F` are mutually inverse up to homotopy relative to
the ends (`Homotopic.trans_symm_trans`, `Homotopic.symm_trans_trans`), and differences satisfy
the cocycle law (`Homotopic.symm_trans_trans_symm_trans`). For a constant map `f₁ = const X y`,
the self-homotopies of `f₁` are the continuous families of loops at `y`
(`ContinuousMap.Homotopy.evalAtEquiv`), and the relation above becomes ordinary homotopy of maps
into the loop space (`ContinuousMap.Homotopy.homotopic_iff_evalAtEquiv`). Together these
identify the classes of nullhomotopies of a map, once one of them is chosen, with the homotopy
classes of maps `X → Ω Y y`.

## Main declarations

* `ContinuousMap.Homotopy.Homotopic`: homotopy of homotopies relative to their ends.
* `ContinuousMap.Homotopy.homotopic_iff_exists`: the same relation as a homotopy on `I × X`.
* `ContinuousMap.Homotopy.Homotopic.of_reparam`: a homotopy is homotopic to its
  reparametrizations.
* `ContinuousMap.Homotopy.Homotopic.trans_assoc`, `trans_refl`, `refl_trans`, `trans_symm`,
  `symm_trans`: the groupoid laws.
* `ContinuousMap.Homotopy.Homotopic.trans_symm_trans`, `symm_trans_trans`: appending and taking
  differences are inverse up to homotopy.
* `ContinuousMap.Homotopy.evalAtEquiv`: homotopies between constant maps are families of paths.
* `ContinuousMap.pathTrans`, `ContinuousMap.pathSymm`: pointwise concatenation and reversal of
  families of paths, which `evalAtEquiv` matches with `Homotopy.trans` and `Homotopy.symm`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

open unitInterval Set

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f₀ f₁ f₂ f₃ : C(X, Y)}

/-! ### Paths traced by concatenated and reversed homotopies -/

@[simp]
theorem evalAt_refl (f : C(X, Y)) (x : X) : (Homotopy.refl f).evalAt x = Path.refl (f x) := by
  ext
  simp

@[simp]
theorem evalAt_symm (F : Homotopy f₀ f₁) (x : X) : F.symm.evalAt x = (F.evalAt x).symm := by
  ext
  simp

@[simp]
theorem evalAt_trans (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (x : X) :
    (F.trans G).evalAt x = (F.evalAt x).trans (G.evalAt x) := by
  ext t
  simp only [evalAt_apply, trans_apply, Path.trans_apply]

@[simp]
theorem symm_refl (f : C(X, Y)) : (Homotopy.refl f).symm = Homotopy.refl f := by
  ext
  simp

/-! ### Homotopy relative to the ends -/

/-- Two homotopies from `f₀` to `f₁` are homotopic when they are homotopic relative to their ends
`{0, 1} × X`: at every point `x`, the paths traced by `x` are homotopic as paths, continuously
in `x`. -/
def Homotopic (F G : Homotopy f₀ f₁) : Prop :=
  F.toContinuousMap.HomotopicRel G.toContinuousMap ({0, 1} ×ˢ univ)

theorem homotopic_def {F G : Homotopy f₀ f₁} :
    F.Homotopic G ↔ F.toContinuousMap.HomotopicRel G.toContinuousMap ({0, 1} ×ˢ univ) :=
  Iff.rfl

/-- A continuous map `H : I × I × X → Y` with `H (0, s, x) = f₀ x` and `H (1, s, x) = f₁ x` is a
homotopy, relative to the ends, from the homotopy `H (·, 0, ·)` to the homotopy `H (·, 1, ·)`. -/
theorem Homotopic.of_continuous {F G : Homotopy f₀ f₁} (H : I × I × X → Y) (hH : Continuous H)
    (hH₀ : ∀ s x, H (0, s, x) = f₀ x) (hH₁ : ∀ s x, H (1, s, x) = f₁ x)
    (hF : ∀ t x, H (t, 0, x) = F (t, x)) (hG : ∀ t x, H (t, 1, x) = G (t, x)) :
    F.Homotopic G := by
  refine ⟨{ toFun p := H (p.2.1, p.1, p.2.2)
            map_zero_left p := hF p.1 p.2
            map_one_left p := hG p.1 p.2
            prop' s := ?_ }⟩
  rintro ⟨t, x⟩ ⟨ht, -⟩
  rcases ht with rfl | rfl <;> simp [hH₀, hH₁]

/-- Homotopies `F G` from `f₀` to `f₁` are homotopic exactly when some homotopy from `f₀ ∘ snd`
to `f₁ ∘ snd` on `I × X` restricts to `F` on `{0} × X` and to `G` on `{1} × X`. -/
theorem homotopic_iff_exists {F G : Homotopy f₀ f₁} :
    F.Homotopic G ↔ ∃ H : Homotopy (f₀.comp .snd) (f₁.comp (.snd : C(I × X, X))),
      (∀ t x, H (t, 0, x) = F (t, x)) ∧ ∀ t x, H (t, 1, x) = G (t, x) := by
  constructor
  · rintro ⟨A⟩
    refine ⟨{ toFun p := A (p.2.1, p.1, p.2.2)
              map_zero_left p := ?_
              map_one_left p := ?_ }, fun t x ↦ A.apply_zero (t, x), fun t x ↦ A.apply_one (t, x)⟩
    · simpa using A.eq_fst p.1 (x := (0, p.2)) (by simp)
    · simpa using A.eq_fst p.1 (x := (1, p.2)) (by simp)
  · rintro ⟨H, h₀, h₁⟩
    exact Homotopic.of_continuous (fun p ↦ H p) H.continuous (fun s x ↦ H.apply_zero (s, x))
      (fun s x ↦ H.apply_one (s, x)) h₀ h₁

/-- The value of Mathlib's `Path.Homotopy.reflTransSymm p` at `(s, t)`: the path `p` at time
`Path.Homotopy.reflTransSymmAux (s, t)`. Mathlib defines `reflTransSymm` as a plain `def` with no
`simps` lemmas, so this unfolds its body, once, for the continuity argument in
`Homotopic.trans_symm`. -/
private theorem reflTransSymm_apply {y₀ y₁ : Y} (p : Path y₀ y₁) (x : I × I) :
    Path.Homotopy.reflTransSymm p x =
      p ⟨Path.Homotopy.reflTransSymmAux x, Path.Homotopy.reflTransSymmAux_mem_I x⟩ :=
  (rfl)

namespace Homotopic

/-- Homotopic homotopies trace homotopic paths through every point. -/
theorem evalAt {F G : Homotopy f₀ f₁} (h : F.Homotopic G) (x : X) :
    (F.evalAt x).Homotopic (G.evalAt x) := by
  obtain ⟨H, h₀, h₁⟩ := homotopic_iff_exists.1 h
  refine ⟨{ toFun p := H (p.2, p.1, x)
            map_zero_left t := h₀ t x
            map_one_left t := h₁ t x
            prop' s := ?_ }⟩
  rintro t (rfl | rfl) <;> simp

@[refl]
theorem refl (F : Homotopy f₀ f₁) : F.Homotopic F :=
  HomotopicRel.refl _

@[symm]
theorem symm ⦃F G : Homotopy f₀ f₁⦄ (h : F.Homotopic G) : G.Homotopic F :=
  HomotopicRel.symm h

@[trans]
theorem trans ⦃F G H : Homotopy f₀ f₁⦄ (h₀ : F.Homotopic G) (h₁ : G.Homotopic H) :
    F.Homotopic H :=
  HomotopicRel.trans h₀ h₁

theorem equivalence : Equivalence (Homotopic : Homotopy f₀ f₁ → Homotopy f₀ f₁ → Prop) :=
  ⟨refl, (symm ·), (trans · ·)⟩

/-- Concatenation of homotopies respects homotopy relative to the ends. -/
theorem hcomp {F F' : Homotopy f₀ f₁} {G G' : Homotopy f₁ f₂} (hF : F.Homotopic F')
    (hG : G.Homotopic G') : (F.trans G).Homotopic (F'.trans G') := by
  obtain ⟨A, hA₀, hA₁⟩ := homotopic_iff_exists.1 hF
  obtain ⟨B, hB₀, hB₁⟩ := homotopic_iff_exists.1 hG
  refine homotopic_iff_exists.2 ⟨A.trans B, fun t x ↦ ?_, fun t x ↦ ?_⟩ <;>
    simp only [trans_apply] <;> split_ifs <;> simp [hA₀, hA₁, hB₀, hB₁]

/-- Reversal of homotopies respects homotopy relative to the ends. -/
theorem symm₂ {F F' : Homotopy f₀ f₁} (h : F.Homotopic F') : F.symm.Homotopic F'.symm := by
  obtain ⟨A, hA₀, hA₁⟩ := homotopic_iff_exists.1 h
  exact homotopic_iff_exists.2 ⟨A.symm, fun t x ↦ by simp [hA₀], fun t x ↦ by simp [hA₁]⟩

/-- A homotopy is homotopic to its reparametrization by an endpoint-preserving map `φ : I → I`. -/
theorem of_reparam {F G : Homotopy f₀ f₁} (φ : I → I) (hφ : Continuous φ) (h₀ : φ 0 = 0)
    (h₁ : φ 1 = 1) (h : ∀ t x, G (t, x) = F (φ t, x)) : F.Homotopic G := by
  refine of_continuous (fun p ↦ F (Icc.convexComb p.1 (φ p.1) p.2.1, p.2.2)) (by fun_prop)
    (fun s x ↦ ?_) (fun s x ↦ ?_) (fun t x ↦ ?_) (fun t x ↦ ?_)
  · simp [h₀]
  · simp [h₁]
  · simp
  · simp [h]

/-- Concatenation of homotopies is associative up to homotopy relative to the ends. -/
theorem trans_assoc (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) (H : Homotopy f₂ f₃) :
    ((F.trans G).trans H).Homotopic (F.trans (G.trans H)) := by
  refine (of_reparam
    (fun t ↦ ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩)
    (by fun_prop) (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
    (Subtype.ext Path.Homotopy.transAssocReparamAux_one) fun t x ↦ ?_).symm
  simpa only [← evalAt_trans, Path.coe_reparam, Function.comp_apply, evalAt_apply] using
    DFunLike.congr_fun
      (Path.Homotopy.trans_assoc_reparam (F.evalAt x) (G.evalAt x) (H.evalAt x)) t

/-- The constant homotopy is a right unit for concatenation up to homotopy relative to the ends. -/
theorem trans_refl (F : Homotopy f₀ f₁) : (F.trans (Homotopy.refl f₁)).Homotopic F := by
  refine (of_reparam
    (fun t ↦ ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩)
    (by fun_prop) (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one) fun t x ↦ ?_).symm
  simpa only [← evalAt_refl, ← evalAt_trans, Path.coe_reparam, Function.comp_apply,
    evalAt_apply] using DFunLike.congr_fun (Path.Homotopy.trans_refl_reparam (F.evalAt x)) t

/-- The constant homotopy is a left unit for concatenation up to homotopy relative to the ends. -/
theorem refl_trans (F : Homotopy f₀ f₁) : ((Homotopy.refl f₀).trans F).Homotopic F := by
  simpa [symm_trans] using (trans_refl F.symm).symm₂

/-- A homotopy followed by its reversal is homotopic, relative to the ends, to the constant
homotopy. -/
theorem trans_symm (F : Homotopy f₀ f₁) : (F.trans F.symm).Homotopic (Homotopy.refl f₀) := by
  refine (of_continuous (F := Homotopy.refl f₀)
    (fun p ↦ Path.Homotopy.reflTransSymm (F.evalAt p.2.2) (p.2.1, p.1)) ?_
    (fun s x ↦ (Path.Homotopy.reflTransSymm (F.evalAt x)).source s)
    (fun s x ↦ (Path.Homotopy.reflTransSymm (F.evalAt x)).target s)
    (fun t x ↦ by simp) (fun t x ↦ by simp [← evalAt_symm, ← evalAt_trans])).symm
  simp only [reflTransSymm_apply, evalAt_apply]
  fun_prop

/-- The reversal of a homotopy followed by the homotopy is homotopic, relative to the ends, to the
constant homotopy. -/
theorem symm_trans (F : Homotopy f₀ f₁) : (F.symm.trans F).Homotopic (Homotopy.refl f₁) := by
  simpa using trans_symm F.symm

/-- Cancellation: following `F₀` by the difference from `F₀` to `G` is homotopic, relative to
the ends, to `G`. -/
theorem trans_symm_trans (F₀ : Homotopy f₀ f₁) (G : Homotopy f₀ f₂) :
    (F₀.trans (F₀.symm.trans G)).Homotopic G :=
  (trans_assoc _ _ _).symm.trans <| (hcomp (trans_symm F₀) (refl G)).trans (refl_trans G)

/-- Cancellation: the difference from `F₀` to `F₀.trans G` is homotopic, relative to the ends,
to `G`. -/
theorem symm_trans_trans (F₀ : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F₀.symm.trans (F₀.trans G)).Homotopic G :=
  (trans_assoc _ _ _).symm.trans <| (hcomp (symm_trans F₀) (refl G)).trans (refl_trans G)

/-- The cocycle law for differences: the difference from `F` to `G` followed by the difference
from `G` to `H` is homotopic, relative to the ends, to the difference from `F` to `H`. -/
theorem symm_trans_trans_symm_trans (F : Homotopy f₀ f₁) (G : Homotopy f₀ f₂)
    (H : Homotopy f₀ f₃) :
    ((F.symm.trans G).trans (G.symm.trans H)).Homotopic (F.symm.trans H) :=
  (trans_assoc _ _ _).trans <| hcomp (refl _) (trans_symm_trans G H)

end Homotopic

/-! ### Homotopies between constant maps -/

/-- A homotopy between the constant maps at `y₀` and `y₁` is a continuous family, indexed by
`X`, of paths from `y₀` to `y₁`: the path traced by each point. -/
def evalAtEquiv {y₀ y₁ : Y} : Homotopy (const X y₀) (const X y₁) ≃ C(X, Path y₀ y₁) where
  toFun F := ⟨F.evalAt, Path.continuous_uncurry_iff.1 (F.continuous.comp continuous_swap)⟩
  invFun α :=
    { toFun p := α p.2 p.1
      continuous_toFun := (Path.continuous_uncurry_iff.2 α.continuous).comp continuous_swap
      map_zero_left := by simp
      map_one_left := by simp }
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem evalAtEquiv_apply {y₀ y₁ : Y} (F : Homotopy (const X y₀) (const X y₁)) (x : X) :
    evalAtEquiv F x = F.evalAt x :=
  (rfl)

@[simp]
theorem evalAt_evalAtEquiv_symm {y₀ y₁ : Y} (α : C(X, Path y₀ y₁)) (x : X) :
    (evalAtEquiv.symm α).evalAt x = α x :=
  (rfl)

@[simp]
theorem evalAtEquiv_symm_apply {y₀ y₁ : Y} (α : C(X, Path y₀ y₁)) (t : I) (x : X) :
    evalAtEquiv.symm α (t, x) = α x t :=
  (rfl)

/-- The constant homotopy at a constant map is the constant family of constant paths. -/
@[simp]
theorem evalAtEquiv_refl (y : Y) :
    evalAtEquiv (Homotopy.refl (const X y)) = const X (Path.refl y) := by
  ext
  simp

/-- The pointwise concatenation of continuous families of paths. -/
noncomputable def _root_.ContinuousMap.pathTrans {y₀ y₁ y₂ : Y} (α : C(X, Path y₀ y₁))
    (β : C(X, Path y₁ y₂)) : C(X, Path y₀ y₂) where
  toFun x := (α x).trans (β x)
  continuous_toFun := α.continuous.path_trans β.continuous

@[simp]
theorem _root_.ContinuousMap.pathTrans_apply {y₀ y₁ y₂ : Y} (α : C(X, Path y₀ y₁))
    (β : C(X, Path y₁ y₂)) (x : X) : α.pathTrans β x = (α x).trans (β x) :=
  (rfl)

/-- The pointwise reversal of a continuous family of paths. -/
def _root_.ContinuousMap.pathSymm {y₀ y₁ : Y} (α : C(X, Path y₀ y₁)) : C(X, Path y₁ y₀) where
  toFun x := (α x).symm
  continuous_toFun := Path.continuous_symm.comp α.continuous

@[simp]
theorem _root_.ContinuousMap.pathSymm_apply {y₀ y₁ : Y} (α : C(X, Path y₀ y₁)) (x : X) :
    α.pathSymm x = (α x).symm :=
  (rfl)

/-- Concatenating homotopies between constant maps concatenates their families of paths. -/
@[simp]
theorem evalAtEquiv_trans {y₀ y₁ y₂ : Y} (F : Homotopy (const X y₀) (const X y₁))
    (G : Homotopy (const X y₁) (const X y₂)) :
    evalAtEquiv (F.trans G) = (evalAtEquiv F).pathTrans (evalAtEquiv G) := by
  ext x : 1
  simp

/-- Reversing a homotopy between constant maps reverses its family of paths. -/
@[simp]
theorem evalAtEquiv_symm {y₀ y₁ : Y} (F : Homotopy (const X y₀) (const X y₁)) :
    evalAtEquiv F.symm = (evalAtEquiv F).pathSymm := by
  ext x : 1
  simp

@[simp]
theorem evalAtEquiv_symm_pathTrans {y₀ y₁ y₂ : Y} (α : C(X, Path y₀ y₁))
    (β : C(X, Path y₁ y₂)) :
    evalAtEquiv.symm (α.pathTrans β) = (evalAtEquiv.symm α).trans (evalAtEquiv.symm β) := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp]
theorem evalAtEquiv_symm_pathSymm {y₀ y₁ : Y} (α : C(X, Path y₀ y₁)) :
    evalAtEquiv.symm α.pathSymm = (evalAtEquiv.symm α).symm := by
  rw [Equiv.symm_apply_eq]
  simp

/-- Homotopies between constant maps are homotopic relative to their ends exactly when their
families of paths are homotopic as maps into the space of paths. -/
theorem homotopic_iff_evalAtEquiv {y₀ y₁ : Y} {F G : Homotopy (const X y₀) (const X y₁)} :
    F.Homotopic G ↔ (evalAtEquiv F).Homotopic (evalAtEquiv G) := by
  rw [homotopic_iff_exists]
  constructor
  · rintro ⟨H, h₀, h₁⟩
    exact ⟨{ toContinuousMap := evalAtEquiv (X := I × X) H
             map_zero_left x := Path.ext <| funext fun t ↦ h₀ t x
             map_one_left x := Path.ext <| funext fun t ↦ h₁ t x }⟩
  · rintro ⟨K⟩
    exact ⟨evalAtEquiv.symm K.toContinuousMap, fun t x ↦ DFunLike.congr_fun (K.apply_zero x) t,
      fun t x ↦ DFunLike.congr_fun (K.apply_one x) t⟩

end ContinuousMap.Homotopy
