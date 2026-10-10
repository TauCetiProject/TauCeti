/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Moore paths and the Moore loop space

A **Moore path** in `X` is a path of variable duration: a length `L ≥ 0` together with a
continuous map `γ : [0, ∞) → X` that is stopped at time `L`, so `γ t = γ L` for `t ≥ L`.
Concatenation adds the lengths and runs the second path after the first, with no
reparametrization.  It is therefore *strictly* associative, and the paths of length zero are
strict units.  This is what makes the Moore loops at a point `x` a monoid on the nose, rather than
a monoid up to homotopy as for loops parametrized by the unit interval.

Moore paths carry the topology of a subspace of `[0, ∞) × C([0, ∞), X)`, with the compact-open
topology on the second factor.  Since `[0, ∞)` is locally compact, a family of Moore paths is
continuous exactly when its lengths and its uncurried paths are (`MoorePath.continuous_iff`).
Concatenation is continuous in this topology (`Continuous.moorePath_trans`), so the Moore loops
at `x` form a topological monoid `MooreLoopSpace X x`, functorial in based maps.

A path does not determine its length: the constant path of any length has the same underlying
map.  So a Moore path is not a bundled function, and equality of Moore paths is checked on the
length and on the path (`MoorePath.ext`).

The Moore loop space is not homeomorphic to Mathlib's loop space `Path x x` of loops parametrized
by the unit interval: when `X` is a point, the Moore loops at it form a copy of `[0, ∞)`.

## Main definitions

* `TauCeti.MoorePath X`: Moore paths in `X`, with `length`, `source` and `target`.
* `TauCeti.MoorePath.refl x`: the constant path at `x` of length zero.
* `TauCeti.MoorePath.trans`: concatenation of two Moore paths with matching endpoints.
* `TauCeti.MoorePath.map`: the image of a Moore path under a continuous map.
* `TauCeti.MooreLoopSpace X x`: the Moore loops at `x`, a monoid under concatenation with unit
  the constant loop of length zero.
* `TauCeti.MooreLoopSpace.map`: the continuous monoid homomorphism induced by a based map.

## Main results

* `TauCeti.MoorePath.trans_assoc`, `TauCeti.MoorePath.refl_trans`,
  `TauCeti.MoorePath.trans_refl`: concatenation is strictly associative and strictly unital.
* `TauCeti.MoorePath.continuous_iff`: the characterization of continuous families of Moore paths.
* `Continuous.moorePath_trans`: concatenation is continuous.
* `TauCeti.MooreLoopSpace.instContinuousMul`: the Moore loop space is a topological monoid.

## References

* J. C. Moore, *Le théorème de Freudenthal, la suite exacte de James et l'invariant de Hopf
  généralisé*, Séminaire Henri Cartan 7 (1954–1955), exposé 22.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
-/

public noncomputable section

open scoped NNReal

namespace TauCeti

/-- A **Moore path** in `X`: a continuous map `[0, ∞) → X` together with a length `L ≥ 0`, such
that the path is stopped from time `L` on. -/
structure MoorePath (X : Type*) [TopologicalSpace X] extends C(ℝ≥0, X) where
  /-- The length, or duration, of the Moore path. -/
  length : ℝ≥0
  /-- The path is stopped from time `length` on. -/
  apply_of_length_le' : ∀ t, length ≤ t → toFun t = toFun length

namespace MoorePath

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

instance : CoeFun (MoorePath X) fun _ ↦ ℝ≥0 → X :=
  ⟨fun γ ↦ γ.toContinuousMap⟩

@[ext]
theorem ext {γ₁ γ₂ : MoorePath X} (hL : γ₁.length = γ₂.length) (h : ∀ t, γ₁ t = γ₂ t) :
    γ₁ = γ₂ := by
  obtain ⟨f₁, L₁, h₁⟩ := γ₁
  obtain ⟨f₂, L₂, h₂⟩ := γ₂
  obtain rfl : f₁ = f₂ := ContinuousMap.ext h
  obtain rfl : L₁ = L₂ := hL
  rfl

@[fun_prop]
protected theorem continuous (γ : MoorePath X) : Continuous γ :=
  γ.toContinuousMap.continuous

/-- The starting point of a Moore path. -/
def source (γ : MoorePath X) : X :=
  γ 0

/-- The end point of a Moore path: its value at time `length`. -/
def target (γ : MoorePath X) : X :=
  γ γ.length

theorem source_def (γ : MoorePath X) : γ.source = γ 0 :=
  (rfl)

theorem target_def (γ : MoorePath X) : γ.target = γ γ.length :=
  (rfl)

/-- A Moore path is stopped at its target from time `length` on. -/
theorem apply_of_length_le (γ : MoorePath X) {t : ℝ≥0} (ht : γ.length ≤ t) : γ t = γ.target :=
  γ.apply_of_length_le' t ht

/-- A Moore path only depends on times up to its length. -/
theorem apply_min_length (γ : MoorePath X) (t : ℝ≥0) : γ (min t γ.length) = γ t := by
  rcases le_total t γ.length with ht | ht
  · rw [min_eq_left ht]
  · rw [min_eq_right ht, γ.apply_of_length_le ht, target_def]

/-! ### The topology of Moore paths -/

/-- Moore paths carry the topology induced by the length and the path, as a subspace of
`[0, ∞) × C([0, ∞), X)` with the compact-open topology on the second factor. -/
instance : TopologicalSpace (MoorePath X) :=
  TopologicalSpace.induced (fun γ ↦ (γ.length, γ.toContinuousMap)) inferInstance

theorem isEmbedding_length_toContinuousMap :
    Topology.IsEmbedding fun γ : MoorePath X ↦ (γ.length, γ.toContinuousMap) where
  eq_induced := rfl
  injective _ _ h := ext (Prod.ext_iff.1 h).1 fun t ↦ congr($((Prod.ext_iff.1 h).2) t)

@[fun_prop]
theorem continuous_length : Continuous (length : MoorePath X → ℝ≥0) :=
  continuous_fst.comp isEmbedding_length_toContinuousMap.continuous

@[fun_prop]
theorem continuous_toContinuousMap :
    Continuous (toContinuousMap : MoorePath X → C(ℝ≥0, X)) :=
  continuous_snd.comp isEmbedding_length_toContinuousMap.continuous

/-- Evaluation of Moore paths is jointly continuous in the path and the time. -/
theorem continuous_eval : Continuous fun p : MoorePath X × ℝ≥0 ↦ p.1 p.2 :=
  ContinuousEval.continuous_eval.comp (continuous_toContinuousMap.prodMap continuous_id)

/-- Evaluation of a continuous family of Moore paths at continuously varying times is
continuous. -/
@[fun_prop]
protected theorem _root_.Continuous.moorePath_eval {f : Y → MoorePath X} {g : Y → ℝ≥0}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y ↦ f y (g y) :=
  continuous_eval.comp (hf.prodMk hg)

/-- A family of Moore paths is continuous exactly when its lengths and its uncurried paths are
continuous. -/
theorem continuous_iff {f : Y → MoorePath X} :
    Continuous f ↔ Continuous (fun y ↦ (f y).length) ∧ Continuous fun p : Y × ℝ≥0 ↦ f p.1 p.2 := by
  refine ⟨fun hf ↦ ⟨continuous_length.comp hf, continuous_eval.comp (hf.prodMap continuous_id)⟩,
    fun ⟨hL, hf⟩ ↦ ?_⟩
  rw [isEmbedding_length_toContinuousMap.continuous_iff]
  exact hL.prodMk (ContinuousMap.continuous_of_continuous_uncurry _ hf)

@[fun_prop]
theorem continuous_source : Continuous (source : MoorePath X → X) :=
  continuous_eval.comp (continuous_id.prodMk continuous_const)

@[fun_prop]
theorem continuous_target : Continuous (target : MoorePath X → X) :=
  continuous_eval.comp (continuous_id.prodMk continuous_length)

/-! ### Constant paths -/

/-- The constant Moore path at `x`, of length zero. -/
def refl (x : X) : MoorePath X where
  toContinuousMap := .const ℝ≥0 x
  length := 0
  apply_of_length_le' _ _ := rfl

@[simp]
theorem refl_apply (x : X) (t : ℝ≥0) : refl x t = x :=
  (rfl)

@[simp]
theorem length_refl (x : X) : (refl x).length = 0 :=
  (rfl)

@[simp]
theorem source_refl (x : X) : (refl x).source = x :=
  (rfl)

@[simp]
theorem target_refl (x : X) : (refl x).target = x :=
  (rfl)

/-- A Moore path of length zero is the constant path at its source. -/
theorem eq_refl_of_length_eq_zero {γ : MoorePath X} (h : γ.length = 0) : γ = refl γ.source := by
  refine ext h fun t ↦ ?_
  rw [γ.apply_of_length_le (h.trans_le zero_le), target_def, h, refl_apply, source_def]

@[fun_prop]
theorem continuous_refl : Continuous (refl : X → MoorePath X) :=
  continuous_iff.2 ⟨continuous_const, continuous_fst⟩

/-! ### Concatenation -/

/-- The path underlying a concatenation: `γ` up to time `γ.length`, then `δ` shifted by
`γ.length`. -/
private def transFun (γ δ : MoorePath X) (t : ℝ≥0) : X :=
  if t ≤ γ.length then γ t else δ (t - γ.length)

private theorem transFun_of_length_le {γ δ : MoorePath X} (h : γ.target = δ.source) {t : ℝ≥0}
    (ht : γ.length ≤ t) : transFun γ δ t = δ (t - γ.length) := by
  rw [transFun]
  split_ifs with ht'
  · rw [le_antisymm ht' ht, tsub_self, ← target_def, h, source_def]
  · rfl

/-- The **concatenation** of two Moore paths with `γ.target = δ.source`: the lengths add, and the
path runs through `γ` and then through `δ`, with no reparametrization. -/
def trans (γ δ : MoorePath X) (h : γ.target = δ.source) : MoorePath X where
  toFun := transFun γ δ
  continuous_toFun := by
    refine Continuous.if_le γ.continuous (δ.continuous.comp (continuous_id.sub continuous_const))
      continuous_id continuous_const fun t ht ↦ ?_
    rw [ht, tsub_self, ← target_def, h, source_def]
  length := γ.length + δ.length
  apply_of_length_le' t ht := by
    have hγ : γ.length ≤ γ.length + δ.length := le_self_add
    rw [transFun_of_length_le h (hγ.trans ht), transFun_of_length_le h hγ, add_tsub_cancel_left,
      δ.apply_of_length_le (le_tsub_of_add_le_left ht), target_def]

theorem trans_apply (γ δ : MoorePath X) (h : γ.target = δ.source) (t : ℝ≥0) :
    γ.trans δ h t = if t ≤ γ.length then γ t else δ (t - γ.length) :=
  (rfl)

@[simp]
theorem length_trans (γ δ : MoorePath X) (h : γ.target = δ.source) :
    (γ.trans δ h).length = γ.length + δ.length :=
  (rfl)

theorem trans_apply_of_le (γ δ : MoorePath X) (h : γ.target = δ.source) {t : ℝ≥0}
    (ht : t ≤ γ.length) : γ.trans δ h t = γ t := by
  rw [trans_apply, ite_eq_left ht]

theorem trans_apply_of_length_le (γ δ : MoorePath X) (h : γ.target = δ.source) {t : ℝ≥0}
    (ht : γ.length ≤ t) : γ.trans δ h t = δ (t - γ.length) :=
  transFun_of_length_le h ht

@[simp]
theorem trans_apply_length_add (γ δ : MoorePath X) (h : γ.target = δ.source) (t : ℝ≥0) :
    γ.trans δ h (γ.length + t) = δ t := by
  rw [trans_apply_of_length_le _ _ _ le_self_add, add_tsub_cancel_left]

@[simp]
theorem source_trans (γ δ : MoorePath X) (h : γ.target = δ.source) :
    (γ.trans δ h).source = γ.source := by
  rw [source_def, trans_apply_of_le _ _ _ zero_le, source_def]

@[simp]
theorem target_trans (γ δ : MoorePath X) (h : γ.target = δ.source) :
    (γ.trans δ h).target = δ.target := by
  rw [target_def, length_trans, trans_apply_length_add, target_def]

/-- Concatenation of Moore paths is strictly associative. -/
theorem trans_assoc (γ δ ε : MoorePath X) (h₁ : γ.target = δ.source) (h₂ : δ.target = ε.source) :
    (γ.trans δ h₁).trans ε (by rwa [target_trans]) =
      γ.trans (δ.trans ε h₂) (by rwa [source_trans]) := by
  refine ext (add_assoc _ _ _) fun t ↦ ?_
  rcases le_total t γ.length with ht | ht
  · rw [trans_apply_of_le _ _ _ (ht.trans le_self_add), trans_apply_of_le _ _ _ ht,
      trans_apply_of_le _ _ _ ht]
  obtain ⟨s, rfl⟩ := exists_add_of_le ht
  rw [trans_apply_length_add]
  rcases le_total s δ.length with hs | hs
  · rw [trans_apply_of_le _ _ _ (by simpa using hs), trans_apply_length_add,
      trans_apply_of_le _ _ _ hs]
  · obtain ⟨u, rfl⟩ := exists_add_of_le hs
    rw [← add_assoc, ← length_trans γ δ h₁, trans_apply_length_add, trans_apply_length_add]

/-- The constant path of length zero is a strict left unit for concatenation. -/
@[simp]
theorem refl_trans {x : X} (γ : MoorePath X) (h : (refl x).target = γ.source) :
    (refl x).trans γ h = γ := by
  refine ext (zero_add _) fun t ↦ ?_
  simpa using trans_apply_length_add (refl x) γ h t

/-- The constant path of length zero is a strict right unit for concatenation. -/
@[simp]
theorem trans_refl {y : X} (γ : MoorePath X) (h : γ.target = (refl y).source) :
    γ.trans (refl y) h = γ := by
  refine ext (add_zero _) fun t ↦ ?_
  rcases le_total t γ.length with ht | ht
  · exact trans_apply_of_le _ _ _ ht
  · rw [trans_apply_of_length_le _ _ _ ht, refl_apply, γ.apply_of_length_le ht, h, source_refl]

end MoorePath

/-- Concatenation of Moore paths is continuous. -/
@[fun_prop]
theorem _root_.Continuous.moorePath_trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : Y → MoorePath X} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ y, (f y).target = (g y).source) : Continuous fun y ↦ (f y).trans (g y) (h y) := by
  refine MoorePath.continuous_iff.2 ⟨by simp only [MoorePath.length_trans]; fun_prop, ?_⟩
  simp only [MoorePath.trans_apply]
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_snd (by fun_prop) fun p hp ↦ ?_
  rw [hp, tsub_self, ← MoorePath.target_def, h, MoorePath.source_def]

namespace MoorePath

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ### Images under continuous maps -/

/-- The image of a Moore path under a continuous map, of the same length. -/
def map (f : C(X, Y)) (γ : MoorePath X) : MoorePath Y where
  toContinuousMap := f.comp γ.toContinuousMap
  length := γ.length
  apply_of_length_le' t ht := congr_arg f (γ.apply_of_length_le' t ht)

@[simp]
theorem map_apply (f : C(X, Y)) (γ : MoorePath X) (t : ℝ≥0) : γ.map f t = f (γ t) :=
  (rfl)

@[simp]
theorem length_map (f : C(X, Y)) (γ : MoorePath X) : (γ.map f).length = γ.length :=
  (rfl)

@[simp]
theorem source_map (f : C(X, Y)) (γ : MoorePath X) : (γ.map f).source = f γ.source :=
  (rfl)

@[simp]
theorem target_map (f : C(X, Y)) (γ : MoorePath X) : (γ.map f).target = f γ.target :=
  (rfl)

@[simp]
theorem map_refl (f : C(X, Y)) (x : X) : (refl x).map f = refl (f x) :=
  (rfl)

@[simp]
theorem map_trans (f : C(X, Y)) (γ δ : MoorePath X) (h : γ.target = δ.source) :
    (γ.trans δ h).map f = (γ.map f).trans (δ.map f) (by simp [h]) := by
  refine ext rfl fun t ↦ ?_
  simp only [map_apply, trans_apply, length_map]
  split_ifs <;> rfl

@[simp]
theorem map_id (γ : MoorePath X) : γ.map (.id X) = γ :=
  (rfl)

theorem map_map (g : C(Y, Z)) (f : C(X, Y)) (γ : MoorePath X) :
    (γ.map f).map g = γ.map (g.comp f) :=
  (rfl)

@[fun_prop]
theorem continuous_map (f : C(X, Y)) : Continuous (map f : MoorePath X → MoorePath Y) :=
  continuous_iff.2 ⟨continuous_length, f.continuous.comp continuous_eval⟩

end MoorePath

/-! ### The Moore loop space -/

/-- The **Moore loop space** of `X` at `x`: the Moore paths from `x` to `x`.  Under concatenation it
is a monoid with unit the constant loop of length zero, and a topological monoid for the subspace
topology. -/
structure MooreLoopSpace (X : Type*) [TopologicalSpace X] (x : X) where
  /-- The underlying Moore path. -/
  toMoorePath : MoorePath X
  /-- The loop starts at `x`. -/
  source_eq : toMoorePath.source = x
  /-- The loop ends at `x`. -/
  target_eq : toMoorePath.target = x

namespace MooreLoopSpace

attribute [simp] source_eq target_eq

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

theorem toMoorePath_injective :
    Function.Injective (toMoorePath : MooreLoopSpace X x → MoorePath X) := by
  rintro ⟨γ, _, _⟩ ⟨δ, _, _⟩ rfl
  rfl

@[ext]
theorem ext {γ δ : MooreLoopSpace X x} (h : γ.toMoorePath = δ.toMoorePath) : γ = δ :=
  toMoorePath_injective h

/-- Moore loops carry the subspace topology of the Moore paths. -/
instance : TopologicalSpace (MooreLoopSpace X x) :=
  TopologicalSpace.induced toMoorePath inferInstance

theorem isEmbedding_toMoorePath :
    Topology.IsEmbedding (toMoorePath : MooreLoopSpace X x → MoorePath X) :=
  ⟨⟨rfl⟩, toMoorePath_injective⟩

@[fun_prop]
theorem continuous_toMoorePath : Continuous (toMoorePath : MooreLoopSpace X x → MoorePath X) :=
  isEmbedding_toMoorePath.continuous

instance : One (MooreLoopSpace X x) :=
  ⟨⟨MoorePath.refl x, MoorePath.source_refl x, MoorePath.target_refl x⟩⟩

instance : Mul (MooreLoopSpace X x) :=
  ⟨fun γ δ ↦ ⟨γ.toMoorePath.trans δ.toMoorePath (by simp), by simp, by simp⟩⟩

@[simp]
theorem toMoorePath_one : (1 : MooreLoopSpace X x).toMoorePath = MoorePath.refl x :=
  (rfl)

@[simp]
theorem toMoorePath_mul (γ δ : MooreLoopSpace X x) :
    (γ * δ).toMoorePath = γ.toMoorePath.trans δ.toMoorePath (by simp) :=
  (rfl)

/-- The Moore loops at `x` form a monoid under concatenation: strict associativity and strict
units of Moore paths. -/
instance : Monoid (MooreLoopSpace X x) where
  mul_assoc γ δ ε := ext (MoorePath.trans_assoc _ _ _ _ _)
  one_mul γ := ext (MoorePath.refl_trans _ _)
  mul_one γ := ext (MoorePath.trans_refl _ _)

/-- The Moore loop space is a topological monoid. -/
instance instContinuousMul : ContinuousMul (MooreLoopSpace X x) where
  continuous_mul := isEmbedding_toMoorePath.continuous_iff.2 <|
    (continuous_toMoorePath.comp continuous_fst).moorePath_trans
      (continuous_toMoorePath.comp continuous_snd) fun p ↦ by simp

/-- The continuous monoid homomorphism of Moore loop spaces induced by a based map. -/
def map (f : C(X, Y)) (hf : f x = y) : MooreLoopSpace X x →ₜ* MooreLoopSpace Y y where
  toFun γ := ⟨γ.toMoorePath.map f, by simp [hf], by simp [hf]⟩
  map_one' := ext <| by simp [hf]
  map_mul' γ δ := ext <| by simp
  continuous_toFun := isEmbedding_toMoorePath.continuous_iff.2 <|
    (MoorePath.continuous_map f).comp continuous_toMoorePath

@[simp]
theorem toMoorePath_map (f : C(X, Y)) (hf : f x = y) (γ : MooreLoopSpace X x) :
    (map f hf γ).toMoorePath = γ.toMoorePath.map f :=
  (rfl)

@[simp]
theorem map_id : map (.id X) rfl = ContinuousMonoidHom.id (MooreLoopSpace X x) :=
  (rfl)

theorem map_comp {Z : Type*} [TopologicalSpace Z] {z : Z} (g : C(Y, Z)) (f : C(X, Y))
    (hg : g y = z) (hf : f x = y) :
    map (g.comp f) (by rw [ContinuousMap.comp_apply, hf, hg]) = (map g hg).comp (map f hf) :=
  (rfl)

end MooreLoopSpace

end TauCeti
