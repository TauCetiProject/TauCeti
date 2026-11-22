/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Symplectic.Annulus.ClosingDefect
public import TauCeti.Topology.Homotopy.Cube.LevelSet

/-!
# The closing block of a chain of twist maps deforms onto a circle of diagonal roots

Let `F_0, …, F_(n-1)` be maps of the strip `ℝ × [0, 1]` commuting with the deck translation
`(x, y) ↦ (x + 1, y)`, with first components `X_k` increasing in the position, increasing in the
momentum for the *positive* factors `k ∈ P` and decreasing for the *negative* ones. In the
finite-action proof of the Poincaré–Birkhoff theorem, a configuration is a starting position
`x` and incoming momenta `y ∈ [0, 1]^n`; it closes up when the closing defect
`G(x, y) = x_n - x` of its broken orbit vanishes (`TauCeti.stripClosingDefect`). Modulo the deck
translation, the closing configurations form the *closing block*, and those with some negative
momentum on a boundary line of the strip form the subset `L` of the block which is the exit set of
the negative gradient flow of the action in the isolating-block argument.

This file splits the momenta `y` into those `u` of the positive factors and those `v` of the
negative factors (`TauCeti.stripInputs`), and reads the closing defect as a family

`G_(x, v)(u)`, `(x, v) ∈ (ℝ / ℤ) × [0, 1]^(n ∖ P)`, `u ∈ [0, 1]^P`

(`TauCeti.annulusClosingDefect`). Then the closing block is the zero level set
`TauCeti.cubeLevelSet` of this family, and its exit set is the preimage of
`(ℝ / ℤ) × ∂[0, 1]^(n ∖ P)` under the projection `(x, v, u) ↦ (x, v)`. This family satisfies the
hypotheses of the deformation of zero level sets onto their diagonal roots
(`TauCeti.cubeLevelSetFiberHomotopyEquiv`):

* it is jointly continuous on the circle, when every `X_k` is continuous on the strip and commutes
  with the deck translation (`TauCeti.continuous_uncurry_annulusClosingDefect`);
* each `G_(x, v)` is strictly increasing on the cube `[0, 1]^P`, when the monotonicity of the
  factors is strict (`TauCeti.strictMono_annulusClosingDefect`): every `X_k` is increasing in the
  position, so a larger positive momentum moves all later positions to the right;
* `G_(x, v)(0) < 0 < G_(x, v)(1)` for every `v`, when the composite chain displaces the lower
  boundary line to the left and the upper one to the right
  (`TauCeti.annulusClosingDefect_zero_neg`, `TauCeti.annulusClosingDefect_one_pos`).

Hence for every `(x, v)` there is exactly one *diagonal root* `t(x, v) · 1` in the cube of positive
momenta at which the broken orbit closes up
(`TauCeti.stripClosingDefect_stripInputs_const_eq_zero_iff`). It lies in the open cube
(`TauCeti.cubeDiagonalRootParam_annulusClosingDefect_mem_Ioo`) and depends continuously on
`(x, v)`, periodically in `x`. The closing block is fibre homotopy equivalent over
`(ℝ / ℤ) × [0, 1]^(n ∖ P)` to its base (`TauCeti.annulusClosingBlockFiberHomotopyEquiv`), through
the deformation moving each closing configuration along the segment to the diagonal root and
correcting it by clamped diagonal shifts. Since the equivalence is fibrewise, it is a homotopy
equivalence of the pair formed by the closing block and `L` with the pair

`((ℝ / ℤ) × [0, 1]^(n ∖ P), (ℝ / ℤ) × ∂[0, 1]^(n ∖ P))`

(`TauCeti.FiberHomotopyEquiv.preimagePairMap` for the subset `univ ×ˢ Cube.boundary _` of the
base), commuting with the projection to the circle. For a chain alternating between `K` negative
and `K` positive factors this is the pair `(S¹ × [0, 1]^K, S¹ × ∂[0, 1]^K)`, whose relative
cohomology in degree `K` carries the class used in the cup-length count of fixed points.

For the chain of the affine shear `(x, y) ↦ (x - (6 y + 1) / 8, y)` followed by the shear
`(x, y) ↦ (x + y, y)`, the diagonal root is `t(x, v) = (6 v + 1) / 8`
(`TauCeti.cubeDiagonalRootParam_annulusClosingDefect_affineShear_shear`).

## Main definitions

* `TauCeti.stripInputs P u v`: the momenta assembled from those of the positive and the negative
  factors.
* `TauCeti.annulusClosingDefect F n P`: the closing defect on `(ℝ / ℤ) × [0, 1]^(n ∖ P)`, as a
  function of the positive momenta.
* `TauCeti.annulusClosingBlockFiberHomotopyEquiv`: the fibre homotopy equivalence of the closing
  block with its base.

## References

* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public noncomputable section

open Set Function unitInterval

namespace TauCeti

variable {F : ℕ → ℝ × ℝ → ℝ × ℝ} {n : ℕ} {P : Set ℕ} [DecidablePred (· ∈ P)]

/-! ### Positive and negative momenta -/

/-- The momenta `y ∈ [0, 1]^n` of a broken orbit of `n` factors, assembled from the momenta `u` of
the positive factors, with indices in `P`, and the momenta `v` of the negative factors. -/
def stripInputs (P : Set ℕ) [DecidablePred (· ∈ P)] (u : {i : Fin n // (i : ℕ) ∈ P} → I)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) : Fin n → ℝ :=
  (Equiv.piEquivPiSubtypeProd (fun i : Fin n ↦ (i : ℕ) ∈ P) fun _ ↦ ℝ).symm
    (fun i ↦ u i, fun i ↦ v i)

theorem stripInputs_apply (u : {i : Fin n // (i : ℕ) ∈ P} → I)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) (i : Fin n) :
    stripInputs P u v i = if h : (i : ℕ) ∈ P then (u ⟨i, h⟩ : ℝ) else v ⟨i, h⟩ :=
  (rfl)

@[simp]
theorem stripInputs_apply_of_mem (u : {i : Fin n // (i : ℕ) ∈ P} → I)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) {i : Fin n} (h : (i : ℕ) ∈ P) :
    stripInputs P u v i = u ⟨i, h⟩ := by
  simp [stripInputs_apply, h]

@[simp]
theorem stripInputs_apply_of_notMem (u : {i : Fin n // (i : ℕ) ∈ P} → I)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) {i : Fin n} (h : (i : ℕ) ∉ P) :
    stripInputs P u v i = v ⟨i, h⟩ := by
  simp [stripInputs_apply, h]

theorem stripInputs_mem_Icc (u : {i : Fin n // (i : ℕ) ∈ P} → I)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) (i : Fin n) : stripInputs P u v i ∈ Icc (0 : ℝ) 1 := by
  rw [stripInputs_apply]
  split_ifs
  exacts [(u _).property, (v _).property]

@[fun_prop]
theorem continuous_stripInputs :
    Continuous fun p : ({i : Fin n // (i : ℕ) ∈ P} → I) × ({i : Fin n // (i : ℕ) ∉ P} → I) ↦
      stripInputs P p.1 p.2 :=
  (Homeomorph.piEquivPiSubtypeProd (fun i : Fin n ↦ (i : ℕ) ∈ P) fun _ ↦ ℝ).symm.continuous.comp
    (by fun_prop)

/-! ### The closing defect on the annulus -/

variable (F n P) in
/-- The **closing defect on the annulus**: at a point `(x, v)` of `(ℝ / ℤ) × [0, 1]^(n ∖ P)` and
positive momenta `u ∈ [0, 1]^P`, the closing defect `G(x, y)` of the broken orbit of the chain
`F 0, …, F (n - 1)` starting at the representative of `x` in `[0, 1)`, with momenta `y` assembled
from `u` and `v`. When the factors commute with the deck translation, the defect does not depend on
the representative (`TauCeti.annulusClosingDefect_coe`). -/
def annulusClosingDefect (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I))
    (u : {i : Fin n // (i : ℕ) ∈ P} → I) : ℝ :=
  stripClosingDefect F n (AddCircle.equivIco 1 0 x.1) (stripInputs P u x.2)

theorem annulusClosingDefect_def (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I))
    (u : {i : Fin n // (i : ℕ) ∈ P} → I) :
    annulusClosingDefect F n P x u =
      stripClosingDefect F n (AddCircle.equivIco 1 0 x.1) (stripInputs P u x.2) :=
  (rfl)

/-- If every factor commutes with the deck translation, the closing defect on the annulus at the
class of `x : ℝ` is the closing defect of the broken orbit starting at `x`. -/
theorem annulusClosingDefect_coe
    (hF : ∀ k < n, ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, (F k (x + 1, t)).1 = (F k (x, t)).1 + 1) (x : ℝ)
    (v : {i : Fin n // (i : ℕ) ∉ P} → I) (u : {i : Fin n // (i : ℕ) ∈ P} → I) :
    annulusClosingDefect F n P ((x : AddCircle (1 : ℝ)), v) u =
      stripClosingDefect F n x (stripInputs P u v) := by
  have hper : Periodic (fun x ↦ stripClosingDefect F n x (stripInputs P u v)) 1 :=
    fun x ↦ stripClosingDefect_add hF (stripInputs_mem_Icc u v)
  rw [annulusClosingDefect_def, AddCircle.coe_equivIco_mk_apply, div_one, mul_one, Int.fract,
    ← mul_one (⌊x⌋ : ℝ)]
  exact hper.sub_int_mul_eq ⌊x⌋

/-- If the first component of every factor is continuous on the strip `ℝ × [0, 1]`, the closing
defect on the annulus is continuous in the positive momenta. -/
theorem continuous_annulusClosingDefect
    (hc : ∀ k < n, ContinuousOn (fun q ↦ (F k q).1) (univ ×ˢ Icc 0 1))
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    Continuous (annulusClosingDefect F n P x) :=
  (contDiffOn_stripClosingDefect (m := 0) fun k hk ↦ contDiffOn_zero.2 (hc k hk))
    |>.continuousOn.comp_continuous (continuous_const.prodMk
      (continuous_stripInputs.comp (continuous_id.prodMk continuous_const)))
      fun _ ↦ ⟨mem_univ _, fun i _ ↦ stripInputs_mem_Icc _ _ i⟩

/-- **Continuity of the closing defect on the annulus.** If the first component of every factor is
continuous on the strip `ℝ × [0, 1]` and commutes with the deck translation, the closing defect on
the annulus is jointly continuous. -/
theorem continuous_uncurry_annulusClosingDefect
    (hc : ∀ k < n, ContinuousOn (fun q ↦ (F k q).1) (univ ×ˢ Icc 0 1))
    (hF : ∀ k < n, ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, (F k (x + 1, t)).1 = (F k (x, t)).1 + 1) :
    Continuous (uncurry (annulusClosingDefect F n P)) := by
  -- Read the defect through the open quotient map `ℝ → ℝ / ℤ` in the first coordinate.
  have hq := (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ))).prodMap
    (IsOpenQuotientMap.id (X := {i : Fin n // (i : ℕ) ∉ P} → I)) |>.prodMap
    (IsOpenQuotientMap.id (X := {i : Fin n // (i : ℕ) ∈ P} → I))
  rw [← hq.continuous_comp_iff]
  have hcomp : uncurry (annulusClosingDefect F n P) ∘
      Prod.map (Prod.map ((↑) : ℝ → AddCircle (1 : ℝ)) id) id =
      fun q ↦ stripClosingDefect F n q.1.1 (stripInputs P q.2 q.1.2) :=
    funext fun q ↦ annulusClosingDefect_coe hF q.1.1 q.1.2 q.2
  rw [hcomp]
  refine (contDiffOn_stripClosingDefect (m := 0) fun k hk ↦ contDiffOn_zero.2 (hc k hk))
    |>.continuousOn.comp_continuous (continuous_fst.fst.prodMk
      (continuous_stripInputs.comp (continuous_snd.prodMk continuous_fst.snd)))
      fun q ↦ ⟨mem_univ _, fun i _ ↦ stripInputs_mem_Icc _ _ i⟩

/-- **The closing defect on the annulus is strictly increasing in the positive momenta**, when
every factor is strictly increasing in the position, and strictly increasing in the momentum for
the positive factors and strictly decreasing for the negative ones. -/
theorem strictMono_annulusClosingDefect
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    StrictMono (annulusClosingDefect F n P x) := fun u u' huu' ↦
  strictMonoOn_stripClosingDefect hx hP hN (v := fun i ↦ x.2 i) (fun i ↦ (x.2 i).property)
    (fun i ↦ (u i).property) (fun i ↦ (u' i).property)
    -- The coercion `[0, 1]^P → ℝ^P` is strictly monotone.
    ((Monotone.strictMono_of_injective
      (f := fun u : {i : Fin n // (i : ℕ) ∈ P} → I ↦ fun i ↦ (u i : ℝ))
      (fun _ _ h i ↦ Pi.le_def.1 h i)
      fun _ _ h ↦ funext fun i ↦ Subtype.ext (congr_fun h i)) huu')

/-- **The closing defect on the annulus is negative on the lower face.** If every factor is
increasing in the position, and increasing in the momentum for the positive factors and decreasing
for the negative ones, and the broken orbit with all momenta `0` ends to the left of its start, then
the closing defect is negative where all positive momenta are `0`, whatever the negative momenta
are. When every factor maps the line `y = 0` into itself, the broken orbit with all momenta `0` is
an orbit of the chain (`TauCeti.stripBrokenOrbitEnd_const_eq_of_orbit`), so the hypothesis says
that the composite chain displaces the lower boundary line to the left. -/
theorem annulusClosingDefect_zero_neg
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₀ : ∀ x, stripClosingDefect F n x 0 < 0)
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    annulusClosingDefect F n P x 0 < 0 := by
  refine (stripClosingDefect_le_stripClosingDefect hx hP hN (stripInputs_mem_Icc 0 x.2)
    (fun _ ↦ ⟨le_rfl, zero_le_one⟩) fun i ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩).trans_lt (h₀ _)
  · simp [h]
  · simpa [h] using (x.2 _).property.1

/-- **The closing defect on the annulus is positive on the upper face.** If every factor is
increasing in the position, and increasing in the momentum for the positive factors and decreasing
for the negative ones, and the broken orbit with all momenta `1` ends to the right of its start,
then the closing defect is positive where all positive momenta are `1`, whatever the negative
momenta are. When every factor maps the line `y = 1` into itself, the hypothesis says that the
composite chain displaces the upper boundary line to the right. -/
theorem annulusClosingDefect_one_pos
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₁ : ∀ x, 0 < stripClosingDefect F n x 1)
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    0 < annulusClosingDefect F n P x 1 := by
  refine (h₁ _).trans_le (stripClosingDefect_le_stripClosingDefect hx hP hN
    (fun _ ↦ ⟨zero_le_one, le_rfl⟩) (stripInputs_mem_Icc 1 x.2) fun i ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩)
  · simp [h]
  · simpa [h] using (x.2 _).property.2

/-! ### The diagonal root -/

/-- Both signs of the closing defect on the faces of the cube of positive momenta, under the strict
monotonicity hypotheses. -/
private lemma annulusClosingDefect_zero_neg_and_one_pos
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₀ : ∀ x, stripClosingDefect F n x 0 < 0) (h₁ : ∀ x, 0 < stripClosingDefect F n x 1)
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    annulusClosingDefect F n P x 0 < 0 ∧ 0 < annulusClosingDefect F n P x 1 :=
  have hx' k hk t ht := (hx k hk t ht).monotone
  have hP' k hk hkP x := (hP k hk hkP x).monotoneOn
  have hN' k hk hkP x := (hN k hk hkP x).antitoneOn
  ⟨annulusClosingDefect_zero_neg hx' hP' hN' h₀ x, annulusClosingDefect_one_pos hx' hP' hN' h₁ x⟩

/-- **The diagonal root closes the broken orbit, and is the only diagonal point that does.** If
some factor is positive, a configuration whose positive momenta all equal `t` closes up exactly
when `t` is the diagonal root parameter `t(x, v)`. -/
theorem stripClosingDefect_stripInputs_const_eq_zero_iff [Nonempty {i : Fin n // (i : ℕ) ∈ P}]
    (hc : ∀ k < n, ContinuousOn (fun q ↦ (F k q).1) (univ ×ˢ Icc 0 1))
    (hF : ∀ k < n, ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, (F k (x + 1, t)).1 = (F k (x, t)).1 + 1)
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₀ : ∀ x, stripClosingDefect F n x 0 < 0) (h₁ : ∀ x, 0 < stripClosingDefect F n x 1)
    (x : ℝ) (v : {i : Fin n // (i : ℕ) ∉ P} → I) (t : I) :
    stripClosingDefect F n x (stripInputs P (fun _ ↦ t) v) = 0 ↔
      t = cubeDiagonalRootParam (annulusClosingDefect F n P) ((x : AddCircle (1 : ℝ)), v) := by
  rw [← annulusClosingDefect_coe hF]
  refine ⟨fun h ↦ (cubeDiagonalRootParam_eq_of_apply_eq_zero
    (strictMono_annulusClosingDefect hx hP hN _) h).symm, ?_⟩
  rintro rfl
  have hsign :=
    annulusClosingDefect_zero_neg_and_one_pos hx hP hN h₀ h₁ ((x : AddCircle (1 : ℝ)), v)
  have h := apply_cubeDiagonalRoot_eq_zero
    (continuous_annulusClosingDefect hc ((x : AddCircle (1 : ℝ)), v)) hsign.1.le hsign.2.le
  rwa [cubeDiagonalRoot_eq_const] at h

/-- **The diagonal root lies in the open cube.** If the broken orbit with all momenta `0` ends to
the left of its start and the one with all momenta `1` to its right, the diagonal root parameter
of the closing defect on the annulus lies in `(0, 1)`. -/
theorem cubeDiagonalRootParam_annulusClosingDefect_mem_Ioo
    (hc : ∀ k < n, ContinuousOn (fun q ↦ (F k q).1) (univ ×ˢ Icc 0 1))
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, Monotone fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, MonotoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, AntitoneOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₀ : ∀ x, stripClosingDefect F n x 0 < 0) (h₁ : ∀ x, 0 < stripClosingDefect F n x 1)
    (x : AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I)) :
    (cubeDiagonalRootParam (annulusClosingDefect F n P) x : ℝ) ∈ Ioo 0 1 :=
  cubeDiagonalRootParam_mem_Ioo (continuous_annulusClosingDefect hc x)
    (annulusClosingDefect_zero_neg hx hP hN h₀ x) (annulusClosingDefect_one_pos hx hP hN h₁ x)

/-! ### The deformation of the closing block -/

/-- **The closing block deforms onto its circle of diagonal roots.** Under the hypotheses of the
strict monotonicity and continuity of the factors, their deck invariance, and the boundary
displacements, the zero level set of the closing defect on the annulus (the *closing block*) is
fibre homotopy equivalent over `(ℝ / ℤ) × [0, 1]^(n ∖ P)` to its base: the projection
`(x, v, u) ↦ (x, v)` and the section `(x, v) ↦ (x, v, t(x, v) · 1)` through the diagonal roots
are inverse fibre homotopy equivalences. -/
def annulusClosingBlockFiberHomotopyEquiv
    (hc : ∀ k < n, ContinuousOn (fun q ↦ (F k q).1) (univ ×ˢ Icc 0 1))
    (hF : ∀ k < n, ∀ x, ∀ t ∈ Icc (0 : ℝ) 1, (F k (x + 1, t)).1 = (F k (x, t)).1 + 1)
    (hx : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1, StrictMono fun x ↦ (F k (x, t)).1)
    (hP : ∀ k < n, k ∈ P → ∀ x, StrictMonoOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (hN : ∀ k < n, k ∉ P → ∀ x, StrictAntiOn (fun t ↦ (F k (x, t)).1) (Icc 0 1))
    (h₀ : ∀ x, stripClosingDefect F n x 0 < 0) (h₁ : ∀ x, 0 < stripClosingDefect F n x 1) :
    FiberHomotopyEquiv (cubeLevelSetProj (annulusClosingDefect F n P))
      (ContinuousMap.id (AddCircle (1 : ℝ) × ({i : Fin n // (i : ℕ) ∉ P} → I))) :=
  cubeLevelSetFiberHomotopyEquiv (continuous_uncurry_annulusClosingDefect hc hF)
    (strictMono_annulusClosingDefect hx hP hN)
    (fun x ↦ (annulusClosingDefect_zero_neg_and_one_pos hx hP hN h₀ h₁ x).1.le)
    (fun x ↦ (annulusClosingDefect_zero_neg_and_one_pos hx hP hN h₀ h₁ x).2.le)

/-! ### A chain of two shears -/

/-- **The diagonal root of a chain of two shears.** For the chain of the affine shear
`(x, y) ↦ (x - (6 y + 1) / 8, y)`, a negative factor, followed by the shear `(x, y) ↦ (x + y, y)`,
a positive factor, the closing defect is `u - (6 v + 1) / 8`
(`TauCeti.stripClosingDefect_affineShear_shear`), so the diagonal root parameter at `(x, v)` is
`(6 v + 1) / 8`, which lies in `[1/8, 7/8]`. -/
theorem cubeDiagonalRootParam_annulusClosingDefect_affineShear_shear (x : AddCircle (1 : ℝ))
    (v : {i : Fin 2 // (i : ℕ) ∉ ({1} : Set ℕ)} → I) :
    (cubeDiagonalRootParam (annulusClosingDefect
      (fun k q ↦ if k = 0 then (q.1 - (6 * q.2 + 1) / 8, q.2) else (q.1 + q.2, q.2)) 2 {1})
      (x, v) : ℝ) = (6 * v ⟨0, by simp⟩ + 1) / 8 := by
  set F : ℕ → ℝ × ℝ → ℝ × ℝ :=
    fun k q ↦ if k = 0 then (q.1 - (6 * q.2 + 1) / 8, q.2) else (q.1 + q.2, q.2)
  have hv := (v ⟨0, by simp⟩).property
  let t : I := ⟨(6 * v ⟨0, by simp⟩ + 1) / 8, by constructor <;> linarith [hv.1, hv.2]⟩
  have hx : ∀ k < 2, ∀ s ∈ Icc (0 : ℝ) 1, StrictMono fun x ↦ (F k (x, s)).1 := by
    intro k _ s _ a b hab
    simp only [F]
    split_ifs <;> linarith
  have hP : ∀ k < 2, k ∈ ({1} : Set ℕ) → ∀ x,
      StrictMonoOn (fun s ↦ (F k (x, s)).1) (Icc 0 1) := by
    rintro k _ rfl x a _ b _ hab
    simp only [F, one_ne_zero, ite_false]
    linarith
  have hN : ∀ k < 2, k ∉ ({1} : Set ℕ) → ∀ x,
      StrictAntiOn (fun s ↦ (F k (x, s)).1) (Icc 0 1) := by
    intro k hk hkP x a _ b _ hab
    obtain rfl : k = 0 := by
      rw [Set.mem_singleton_iff] at hkP
      omega
    simp only [F, ite_true]
    linarith
  have hinputs : stripInputs {1} (fun _ ↦ t) v = ![(v ⟨0, by simp⟩ : ℝ), (t : ℝ)] := by
    ext i
    fin_cases i <;> simp
  have hroot : annulusClosingDefect F 2 {1} (x, v) (fun _ ↦ t) = 0 := by
    rw [annulusClosingDefect_def, hinputs, stripClosingDefect_affineShear_shear]
    simp [t]
  have : Nonempty {i : Fin 2 // (i : ℕ) ∈ ({1} : Set ℕ)} := ⟨⟨1, by simp⟩⟩
  rw [cubeDiagonalRootParam_eq_of_apply_eq_zero (strictMono_annulusClosingDefect hx hP hN _) hroot]

end TauCeti
